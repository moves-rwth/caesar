import * as fs from 'fs/promises';
import * as path from 'path';
import * as  tar from 'tar';
import { ExtensionContext, commands, window } from 'vscode';
import { Octokit } from '@octokit/rest';
import * as AdmZip from 'adm-zip';
import got from 'got';
import { InstallerConfig } from './Configuration';
import * as os from 'os';
import { Verifier } from './Verifier';


export class ServerInstaller {
    private context: ExtensionContext;
    private verifier: Verifier;
    private installRoot: string;

    public constructor(context: ExtensionContext, verifier: Verifier) {
        this.context = context;
        this.verifier = verifier;
        this.installRoot = path.join(context.globalStoragePath, "caesar-download");

        commands.registerCommand('caesar.checkUpdate', async () => {
            await this.checkForUpdateOrInstall(false);
        });

        commands.registerCommand('caesar.uninstall', async () => {
            await this.uninstall(true);
        });
    }

    public async regularlyCheckForUpdatesIfEnabled(): Promise<boolean> {
        const enabled: boolean = InstallerConfig.get("autoCheck");
        if (enabled) {
            const CHECK_INTERVAL = 24 * 60 * 60 * 1000; // 24 hours in milliseconds
            const lastCheck = this.context.globalState.get<number>('lastDependencyCheck');
            const now = Date.now();
            // Check if it's time to perform another check
            if (lastCheck && now - lastCheck < CHECK_INTERVAL) {
                return false;
            }
            await this.checkForUpdateOrInstall(true);
            await this.context.globalState.update('lastDependencyCheck', now);
            return true;
        }
        return false;
    }

    public async getServerExecutable(): Promise<string | null> {
        const binaryPath = path.join(this.installRoot, "caesar");
        try {
            await fs.access(binaryPath, fs.constants.X_OK);
            return binaryPath;
        } catch (err) {
            await this.context.globalState.update('lastDependencyCheck', undefined);
            await this.context.globalState.update("installedVersion", undefined);
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
        const release = await getLatestReleaseAsset("moves-rwth", "caesar", prerelease, assetFilter);
        const currentVersion = this.context.globalState.get("installedVersion");
        if (currentVersion === hashRelease(release)) {
            if (notifyNoNewVersion) {
                void window.showInformationMessage(`No new version of Caesar available. You're up to date with ${release.releaseName} (${release.date}).`);
            }
            return;
        }
        const isInstalled = (await this.getServerExecutable()) !== null;
        const message = isInstalled ? `New version of Caesar available: ${release.releaseName} (${release.date})` : `Caesar is not installed. Do you want to install Caesar (${release.releaseName}, ${release.date})?`;
        const button = isInstalled ? "Update" : "Install";
        const selected = await window.showInformationMessage(message, button);
        if (selected === button) {
            await this.downloadAsset(release);
        }
    }

    public async uninstall(notifyUninstalled: boolean) {
        if (notifyUninstalled) {
            if ((await this.getServerExecutable()) === null) {
                return;
            }
        }
        await this.verifier.client.stop();
        await fs.rm(this.installRoot, { recursive: true, force: true, maxRetries: 5 });
        if (notifyUninstalled) {
            void window.showInformationMessage("Removed Caesar binary.");
        }
    }

    private async downloadAsset(release: ReleaseAsset) {
        await this.uninstall(false);
        await fs.mkdir(this.installRoot, { recursive: true });
        const response = await got.get(release.url, {
            headers: {
                // must be set to download the binary, otherwise we get release JSON info
                Accept: 'application/octet-stream',
            },
        });

        const assetPath = path.join(this.installRoot, `asset.${release.extension}`);
        // TODO: this will load the file first completely into memory
        const data = response.rawBody;
        await fs.writeFile(assetPath, new Uint8Array(data));

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

        await this.context.globalState.update("installedVersion", hashRelease(release));
        void window.showInformationMessage(`Caesar (${release.releaseName}, ${release.date}) installed successfully.`);
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

async function getLatestReleaseAsset(owner: string, repo: string, prerelease: boolean, assetNameIncludes: string): Promise<ReleaseAsset> {
    const octokit = new Octokit();

    try {
        const response = await octokit.repos.listReleases({
            owner: owner,
            repo: repo,
        });

        const releases = response.data;

        for (const release of releases) {
            if (release.draft || (release.prerelease && !prerelease)) {
                continue;
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
    throw new Error(`Could not find any release for this platform`);
}

function getPlatformAssetFilter(): string | null {
    const platform = os.platform();
    const arch = os.arch();
    switch (platform) {
        case "linux":
            if (arch === "x64") {
                return "x86_64-unknown-linux";
            } else {
                return null;
            }
        case "win32":
            if (arch === "x64") {
                return "x86_64-pc-windows";
            } else {
                return null;
            }
        case "darwin":
            if (arch === "x64") {
                return "x86_64-apple-darwin";
            } else if (arch === "arm64") {
                return "aarch64-apple-darwin";
            } else {
                return null;
            }
        default:
            console.log(`Unsupported platform: ${platform}`);
            return null;
    }
}