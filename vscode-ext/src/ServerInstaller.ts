import * as fs from 'fs/promises';
import * as path from 'path';
import * as  tar from 'tar';
import { ExtensionContext, Progress, ProgressLocation, Uri, commands, env, window } from 'vscode';
import { Octokit } from '@octokit/rest';
import * as AdmZip from 'adm-zip';
import got from 'got';
import { InstallerConfig } from './Config';
import { Verifier } from './Verifier';
import * as semver from 'semver';
import { getExtensionVersion, getPlatformAssetExecutableName, getPlatformAssetFilter, isPatchCompatible } from './version';

export class ServerInstaller {
    readonly CAESAR_GITHUB_USER = "moves-rwth";
    readonly CAESAR_GITHUB_REPO = "caesar";
    readonly GLOBAL_STORAGE_DIR = "caesar-download";
    readonly CHECK_INTERVAL_MILLIS = 24 * 60 * 60 * 1000; // 24 hours

    private context: ExtensionContext;
    private verifier: Verifier;
    private installRoot: string;

    public constructor(context: ExtensionContext, verifier: Verifier) {
        this.context = context;
        this.verifier = verifier;
        this.installRoot = path.join(context.globalStoragePath, this.GLOBAL_STORAGE_DIR);

        commands.registerCommand('caesar.checkUpdate', async () => {
            try {
                await this.checkForUpdateOrInstall(true);
            } catch (err) {
                if (!(err instanceof Error)) { throw err; }
                // this command is invoked from a walkthrough. when called from
                // walkthroughs or markdown links, command errors are not shown
                // to the user. so we need to do it manually.
                void window.showErrorMessage(`Failed to check for Caesar updates: ${err.message}`);
                this.verifier.logger.error("Installer: failed to check for updates!", err);
            }
        });

        commands.registerCommand('caesar.uninstall', async () => {
            await this.uninstall(true);
        });
    }

    public async regularlyCheckForUpdatesIfEnabled(): Promise<boolean> {
        const enabled: boolean = InstallerConfig.get("autoCheck");
        if (enabled) {
            const lastCheck = this.context.globalState.get<number>('lastDependencyCheck');
            const now = Date.now();
            // Check if it's time to perform another check
            if (lastCheck && now - lastCheck < this.CHECK_INTERVAL_MILLIS) {
                return false;
            }
            try {
                this.verifier.logger.info("Installer: checking for updates");
                await this.checkForUpdateOrInstall(false);
            } catch (error) {
                console.log(error);
                return true;
            }
            await this.context.globalState.update('lastDependencyCheck', now);
            return true;
        }
        return false;
    }

    public async getServerExecutable(): Promise<string | null> {
        const binaryName = getPlatformAssetExecutableName();
        if (binaryName === null) {
            return null;
        }
        const binaryPath = path.join(this.installRoot, binaryName);
        try {
            await fs.access(binaryPath, fs.constants.X_OK);
            return binaryPath;
        } catch (err) {
            if (!(err instanceof Error)) { throw err; }
            this.verifier.logger.info(`Failed to access server executable at ${binaryPath}: ${err.message}`);
            await this.uninstall(false);
            return null;
        }
    }

    public async checkForUpdateOrInstall(notifyNoNewVersion: boolean) {
        const assetFilter = getPlatformAssetFilter();
        if (assetFilter === null) {
            void window.showErrorMessage("We do not provide Caesar binaries for your platform. Please provide your own binary or compile from source. Change the `caesar.server.installationOptions` setting accordingly.", "Open settings").then(async (command) => {
                if (command === "Open settings") {
                    await commands.executeCommand('workbench.action.openSettings', 'caesar.server');
                }
            });
            return;
        }

        const prerelease: boolean = InstallerConfig.get("nightly");
        const release = await this.getLatestReleaseAsset(prerelease, assetFilter);

        if (release === null) {
            this.verifier.logger.info("Installer: No binary available for platform");
            if (notifyNoNewVersion) {
                void window.showInformationMessage(`There is no Caesar binary for your platform available. Refer to our installation instructions for other options`, "Go to installation instructions").then(async (button) => {
                    if (button === "Go to installation instructions") {
                        await env.openExternal(Uri.parse("https://www.caesarverifier.org/docs/getting-started/installation"));
                    }
                });
            }
            return;
        }

        const currentVersion: string | undefined = this.context.globalState.get("installedVersion");
        if (currentVersion === hashRelease(release)) {
            this.verifier.logger.info(`Installer: Current version ${currentVersion} is up to date with ${release.releaseName}`);
            if (notifyNoNewVersion) {
                void window.showInformationMessage(`No new version of Caesar available. You're up to date with ${release.releaseName} (${release.date}).`);
            }
            return;
        }
        this.verifier.logger.info(`Installer: Current version ${currentVersion} can be updated to new version ${release.releaseName}`);
        const isInstalled = (await this.getServerExecutable()) !== null;
        const message = isInstalled ? `New version of Caesar available: ${release.releaseName} (${release.date})` : `Do you want to install Caesar (${release.releaseName}, ${release.date})?`;
        const button = isInstalled ? "Update" : "Install";
        const selected = await window.showInformationMessage(message, button);
        if (selected === button) {
            await this.installAsset(release);
        }
    }

    public async uninstall(notifyUninstalled: boolean) {
        this.verifier.logger.info("Installer: uninstalling Caesar binary");
        await this.verifier.client.stop();
        await fs.rm(this.installRoot, { recursive: true, force: true, maxRetries: 5 });
        await this.context.globalState.update('lastDependencyCheck', undefined);
        await this.context.globalState.update("installedVersion", undefined);
        await this.verifier.walkthrough.setBinaryInstalled(false);
        if (notifyUninstalled) {
            void window.showInformationMessage("Removed Caesar binary.");
        }
    }

    private async installAsset(release: ReleaseAsset) {
        await window.withProgress({
            location: ProgressLocation.Notification,
            title: "Installing Caesar",
            cancellable: false
        }, async (progress) => {
            try {
                await this.installAssetWithProgress(release, progress);
            } catch (err) {
                // make the progress disappear on error
                progress.report({ increment: 100 });
                throw err;
            }
        });
    }

    private async installAssetWithProgress(release: ReleaseAsset, progress: Progress<{ increment: number, message: string }>) {
        this.verifier.logger.info(`Installer: downloading ${release.releaseName} (${release.url})`);
        progress.report({ increment: 0, message: "Cleaning up old installation..." });

        await this.uninstall(false);

        progress.report({ increment: 25, message: "Downloading..." });

        await fs.mkdir(this.installRoot, { recursive: true });
        // TODO: this will load the file first completely into memory
        const response = await got.get(release.url, {
            headers: {
                // must be set to download the binary, otherwise we get release JSON info
                Accept: 'application/octet-stream',
            },
        });

        const assetPath = path.join(this.installRoot, `asset.${release.extension}`);
        const data = response.rawBody;
        await fs.writeFile(assetPath, new Uint8Array(data));

        this.verifier.logger.info(`Installer: downloaded release. extracting ${assetPath}`);
        progress.report({ increment: 40, message: "Unpacking..." });

        if (release.extension === "zip") {
            const zip = new AdmZip(assetPath);
            await new Promise<void>((resolve, reject) =>
                zip.extractAllToAsync(this.installRoot, true, true, (error) => {
                    if (error) {
                        reject(error);
                    } else {
                        resolve();
                    }
                }
                ));
        } else if (release.extension === "tar.gz") {
            await tar.extract({
                file: assetPath,
                cwd: this.installRoot,
                strip: 1,
            });
        } else {
            throw new Error("unknown ending");
        }

        this.verifier.logger.info(`Installer: extraction done, starting server`);
        progress.report({ increment: 25, message: "Starting server..." });

        await this.context.globalState.update("installedVersion", hashRelease(release));
        await this.verifier.client.start(false);

        this.verifier.logger.info(`Installer: server started.`);
        progress.report({ increment: 100, message: `Successfully installed ${release.releaseName}` });
        // the progress message disappears after completion
        void window.showInformationMessage(`Successfully installed Caesar ${release.releaseName}`);
    }

    async getLatestReleaseAsset(prerelease: boolean, assetNameIncludes: string): Promise<ReleaseAsset | null> {
        const currentSemver = getExtensionVersion(this.context);

        const octokit = new Octokit();

        try {
            const response = await octokit.repos.listReleases({
                owner: this.CAESAR_GITHUB_USER,
                repo: this.CAESAR_GITHUB_REPO,
            });

            const releases = response.data;

            for (const release of releases) {
                if (release.draft) {
                    continue;
                } else if (release.prerelease) {
                    if (!prerelease) {
                        this.verifier.logger.info(`Installer: skipping pre-release ${release.name} (${release.published_at})`);
                        continue;
                    }
                } else {
                    const releaseSemver = semver.parse(release.tag_name);
                    if (!releaseSemver || !isPatchCompatible(currentSemver, releaseSemver)) {
                        this.verifier.logger.info(`Installer: ${releaseSemver?.toString()} incompatible with current extension version ${currentSemver.toString()}`);
                        continue;
                    }
                }

                for (const asset of release.assets) {
                    if (asset.name.includes(assetNameIncludes)) {
                        let extension;
                        if (asset.name.endsWith(".zip")) {
                            extension = "zip";
                        } else if (asset.name.endsWith("tar.gz")) {
                            extension = "tar.gz";
                        } else {
                            throw new Error(`Unsupported file type for asset: ${asset.name}`);
                        }
                        return {
                            releaseName: release.name || "(no name)",
                            date: asset.updated_at,
                            url: asset.url,
                            extension
                        };
                    }
                }
            }
        } catch (error: any) {
            throw new Error(`Failed to fetch releases or process assets: ${error}`);
        }
        return null;
    }
}

interface ReleaseAsset {
    releaseName: string,
    date: string,
    url: string,
    extension: string,
};

function hashRelease(asset: ReleaseAsset): string {
    return `${asset.releaseName}-${asset.date}`;
}
