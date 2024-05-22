import { LanguageClientOptions, ResponseError, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Executable, LanguageClient, ServerOptions } from "vscode-languageclient/node";
import { ExtensionContext, Range, TextDocument } from "vscode";
import * as vscode from "vscode";
import { ConfigurationConstants } from "./constants";
import { CaesarConfig, ServerConfig } from "./Config";
import * as path from "path";
import * as fs from 'fs/promises';
import { ServerInstaller } from "./ServerInstaller";
import * as semver from 'semver';
import { isPatchCompatible } from "./version";
import { WalkthroughComponent } from "./WalkthroughComponent";
import Logger from "./Logger";

export enum ServerStatus {
    Stopped,
    Starting,
    Ready,
    FailedToStart,
    Verifying,
    Finished
}

export enum VerifyResult {
    Verified = "verified",
    Failed = "failed",
    Unknown = "unknown"
}

export interface VerifyStatusNotification {
    document: VersionedTextDocumentIdentifier;
    statuses: [vscode.Range, VerifyResult][];
}

export interface ComputedPreNotification {
    document: VersionedTextDocumentIdentifier;
    pres: [vscode.Range, boolean, [string, string][]][];
}


export class CaesarClient {
    private logger: Logger;
    private walkthrough: WalkthroughComponent;
    private installer: ServerInstaller;
    private client: LanguageClient | null = null;
    private context: ExtensionContext;
    private statusListeners = new Array<(status: ServerStatus) => void>();
    private updateListeners = new Array<(document: TextDocumentIdentifier, results: [Range, VerifyResult][]) => void>();
    private computedPreListeners = new Array<(update: ComputedPreNotification) => void>();
    private needsRestart = false;

    constructor(context: ExtensionContext, logger: Logger, walkthrough: WalkthroughComponent, installer: ServerInstaller) {
        this.context = context;
        this.walkthrough = walkthrough;
        this.installer = installer;
        this.logger = logger;

        // listen to commands
        vscode.commands.registerCommand('caesar.restartServer', async () => {
            await this.restart();
        });

        vscode.commands.registerCommand('caesar.startServer', async () => {
            await this.start(true);
        });

        vscode.commands.registerCommand('caesar.stopServer', async () => {
            await this.stop();
        });

        vscode.commands.registerCommand('caesar.verify', async () => {
            await this.start(true);
            const openEditor = vscode.window.activeTextEditor;
            if (openEditor) {
                await this.verify(openEditor.document);
            } else {
                void vscode.window.showErrorMessage("There is no active text editor");
            }
        });

        vscode.commands.registerCommand('caesar.copyCommand', async () => {
            await this.copyCommand();
        });

        vscode.commands.registerCommand('caesar.showOutput', () => {
            this.client?.outputChannel.show();
        });

        const explainToggleCommandHandler = (setting: string) => {
            return async () => {
                const key = ConfigurationConstants.explainVc;
                const explainVc: string = ServerConfig.get(key);
                if (explainVc === setting) {
                    await ServerConfig.update(key, "no");
                    void vscode.window.showInformationMessage("Explanation of verification conditions disabled.");
                } else {
                    await ServerConfig.update(key, setting);
                    void vscode.window.showInformationMessage("VC explanations enabled. This will slow down verification! Run command again to disable.");
                }
                await this.restart();
                const openEditor = vscode.window.activeTextEditor;
                if (openEditor) {
                    await this.verify(openEditor.document);
                }
            };
        };

        vscode.commands.registerCommand('caesar.explainVc', explainToggleCommandHandler("explain"));
        vscode.commands.registerCommand('caesar.explainCoreVc', explainToggleCommandHandler("core"));

        this.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (ServerConfig.isAffected(e)) {
                this.needsRestart = true;
            }
        }));
    }

    private async createClient(recommendInstallation: boolean): Promise<LanguageClient | null> {
        const context = this.context;

        // Get the source code / binary path from the configurations
        const executable = await this.getExecutable(recommendInstallation);
        if (executable === null) {
            return null;
        }
        const serverOptions: ServerOptions = {
            run: executable,
            debug: executable,
        };

        const initializationOptions = {
            // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access
            "vscodeExtensionVersion": context.extension.packageJSON["version"],
        };
        // Options to control the language client
        const clientOptions: LanguageClientOptions = {
            diagnosticCollectionName: 'caesar',
            // Register the server for heyvl documents
            documentSelector: [{ scheme: 'file', language: 'heyvl' }],
            synchronize: {
                // Notify the server about file changes to '.heyvl' files contained in the workspace
                fileEvents: vscode.workspace.createFileSystemWatcher('**/*.heyvl')
            },
            initializationOptions,
            outputChannel: this.logger.outputChannel,
        };

        const client = new LanguageClient(
            'caesar',
            'Caesar',
            serverOptions,
            clientOptions
        );

        context.subscriptions.push(client);

        // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access
        const extensionVersion: string = context.extension.packageJSON.version;
        client.info(`Starting Caesar for VSCode ${extensionVersion}.`);

        // set up listeners for our custom events
        context.subscriptions.push(client.onNotification("custom/verifyStatus", (params: VerifyStatusNotification) => {
            for (const listener of this.updateListeners) {
                listener(params.document, params.statuses);
            }
        }));

        context.subscriptions.push(client.onNotification("custom/computedPre", (params: ComputedPreNotification) => {
            for (const listener of this.computedPreListeners) {
                listener(params);
            }
        }));

        // listen to onDidSaveTextDocument events
        const autoVerify: string = CaesarConfig.get(ConfigurationConstants.automaticVerification);
        if (autoVerify === "onsave") {
            context.subscriptions.push(vscode.workspace.onDidSaveTextDocument((document) => {
                if (document.languageId !== "heyvl") {
                    return;
                }
                void this.verify(document);
            }));
        }

        // check server version
        context.subscriptions.push(client.onNotification("custom/caesarReady", (event) => {
            // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access
            const serverVersion: string = event["version"];
            const serverSemver = semver.parse(serverVersion);
            const clientSemver = semver.parse(extensionVersion);
            if (!serverSemver || !clientSemver) {
                return;
            }
            if (!isPatchCompatible(serverSemver, clientSemver)) {
                void vscode.window.showWarningMessage(`Caesar for VSCode (${extensionVersion}) and Caesar server (${serverVersion}) have incompatible versions. You might see bugs. Consider updating both the extension and the server.`, "Update server").then(async (button) => {
                    if (button === "Update server") {
                        await this.installer.checkForUpdateOrInstall(true);
                    }
                });
            }
        }));

        return client;
    }

    private async getExecutable(recommendInstallation: boolean): Promise<Executable | null> {
        let serverDirectory: string | undefined;
        let serverExecutable;
        const args: string[] = [];
        switch (ServerConfig.get(ConfigurationConstants.installationOptions)) {
            case ConfigurationConstants.installerBinaryOption: {
                let pathRes = await this.installer.getServerExecutable();
                if (pathRes) {
                    serverExecutable = pathRes;
                } else {
                    if (recommendInstallation) {
                        await this.installer.checkForUpdateOrInstall(true);
                        pathRes = await this.installer.getServerExecutable();
                    }
                    if (!pathRes) {
                        if (recommendInstallation) {
                            void vscode.window.showErrorMessage("The Caesar server binary is required. Either re-try the download, or change the settings to use another installation method.", "Re-try installation", "Open settings").then(async (command) => {
                                if (command === "Open settings") {
                                    await vscode.commands.executeCommand('workbench.action.openSettings', 'caesar.server');
                                } else if (command === "Re-try installation") {
                                    void this.installer.checkForUpdateOrInstall(true);
                                }
                            });
                        }
                        return null;
                    } else {
                        serverExecutable = pathRes;
                    }
                }
                args.push('--language-server');
            }
                break;
            case ConfigurationConstants.userBinaryOption:
                serverExecutable = ServerConfig.get(ConfigurationConstants.binaryPath);
                if (serverExecutable === "") {
                    void vscode.window.showErrorMessage("Caesar: Binary path is not set. Please set the path in the settings.", "Open settings").then(async () => {
                        await vscode.commands.executeCommand('workbench.action.openSettings', 'caesar.server');
                    });
                    throw new Error("Installation path is not set");
                }
                args.push('--language-server');
                break;
            case ConfigurationConstants.sourceCodeOption:
                serverDirectory = ServerConfig.get(ConfigurationConstants.sourcePath);
                if (serverDirectory === "" || serverDirectory === undefined) {
                    void vscode.window.showErrorMessage("Caesar: Source path is not set. Please set the path in the settings.", "Open settings").then(async () => {
                        await vscode.commands.executeCommand('workbench.action.openSettings', 'caesar.server');
                    });
                    throw new Error("Installation path is not set");
                }
                try {
                    const cargoTomlPath = path.join(serverDirectory, "Cargo.toml");
                    await fs.access(cargoTomlPath, fs.constants.R_OK);
                } catch (_error) {
                    void vscode.window.showErrorMessage("Caesar: Cargo.toml file is not found in the path. Please check the path in the settings.");
                    throw new Error("Cargo.toml file is not found in the path");
                }
                serverExecutable = "cargo";
                args.push('run', '--', '--language-server');
                break;
            default:
                throw new Error(`Unknown config setting`);
        }

        args.push("--debug"); // print debug information

        let userArgs: string = ServerConfig.get(ConfigurationConstants.args);
        userArgs = userArgs.trim();
        if (userArgs.length > 0) {
            args.push(...userArgs.split(" "));
        }

        const timeout: string = ServerConfig.get(ConfigurationConstants.timeout);
        // The timeout in args configuration overwrites the timeout configuration.
        if (userArgs.indexOf("--timeout") !== -1) {
            args.push("--timeout", timeout);
        }

        const sliceVerify: boolean = ServerConfig.get(ConfigurationConstants.sliceVerify);
        if (sliceVerify) {
            args.push("--slice-verify");
        }

        const explainVc: string = ServerConfig.get(ConfigurationConstants.explainVc);
        if (explainVc) {
            switch (explainVc) {
                case "explain":
                    args.push("--explain-vc");
                    break;
                case "core":
                    args.push("--explain-core-vc");
                    break;
            }
        }

        return {
            command: serverExecutable,
            args: args,
            options: {
                cwd: serverDirectory,
                env: {
                    ...process.env,
                    "NO_COLOR": "1",
                    "RUST_LOG": "caesar=info",
                    "RUST_BACKTRACE": "1"
                },
            }
        };
    }

    async start(recommendInstallation: boolean): Promise<boolean> {
        if (this.client?.isRunning()) {
            if (this.needsRestart) {
                await this.stop();
            } else {
                return true;
            }
        }

        console.log("Starting Caesar");
        this.notifyStatusUpdate(ServerStatus.Starting);

        try {
            this.client = await this.createClient(recommendInstallation);
            if (this.client === null) {
                this.notifyStatusUpdate(ServerStatus.FailedToStart);
                return false;
            }
        } catch (error) {
            if (!(error instanceof Error)) { throw error; }
            this.notifyStatusUpdate(ServerStatus.FailedToStart);
            this.logger.error("Failed to initialize Caesar.", error);
            void this.logger.showErrorMessage(`Failed to initialize Caesar: ${error.message})`);
            this.client = null;
            return false;
        }

        try {
            await this.client.start();
        } catch (error) {
            if (!(error instanceof Error)) { throw error; }
            this.logger.error("Failed to initialize Caesar.", error);
            void this.logger.showErrorMessage(`Failed to start Caesar: ${error.message})`);
            this.notifyStatusUpdate(ServerStatus.FailedToStart);
            return false;
        }
        this.notifyStatusUpdate(ServerStatus.Ready);
        await this.walkthrough.setBinaryInstalled(true);
        return true;
    }

    async restart() {
        await this.stop();
        await this.start(true);
    }

    async stop() {
        this.needsRestart = false;
        if (!this.client?.isRunning()) {
            return;
        }
        console.log("Stopping Caesar");
        try {
            await this.client.stop();
            await this.client.dispose();
            this.client = null;
        } catch (error) {
            console.error("Failed to stop Caesar", error);
        };
        this.notifyStatusUpdate(ServerStatus.Stopped);
    }

    async verify(document: TextDocument) {
        if (!this.client?.isRunning()) {
            return;
        }
        if (document.languageId !== 'heyvl') {
            void vscode.window.showErrorMessage("Caesar can only verify HeyVL files");
            return;
        }
        const documentItem = {
            uri: document.uri.toString(),
            languageId: document.languageId,
            version: document.version,
            text: document.getText()
        };
        this.notifyStatusUpdate(ServerStatus.Verifying);
        try {
            await this.client.sendRequest('custom/verify', { text_document: documentItem });
            this.notifyStatusUpdate(ServerStatus.Finished);
            await this.walkthrough.setVerifiedHeyVL(true);
        } catch (error) {
            if (!(error instanceof ResponseError)) { throw error; }
            void vscode.window.showErrorMessage(`Verification had an error: ${error.message}`);
            this.notifyStatusUpdate(ServerStatus.Ready);
        }
    }

    private async copyCommand() {
        const executable = await this.getExecutable(true);
        if (executable === null) {
            return;
        }
        const command = '"' + executable.command.replace(/(["'$`\\])/g, '\\$1') + '"';
        let line = `${command} ${executable.args!.join(" ")}`;
        let cwd = executable.options && executable.options.cwd;
        if (cwd !== undefined) {
            cwd = '"' + cwd.replace(/(["'$`\\])/g, '\\$1') + '"';
            line = `pushd ${cwd}; ${line}; popd`;
        }
        await vscode.env.clipboard.writeText(line);
    }

    public onStatusUpdate(callback: (status: ServerStatus) => void) {
        this.statusListeners.push(callback);
    }

    private notifyStatusUpdate(status: ServerStatus) {
        for (const listener of this.statusListeners) {
            listener(status);
        }
    }

    public onVerifyResult(callback: (document: TextDocumentIdentifier, results: [Range, VerifyResult][]) => void) {
        this.updateListeners.push(callback);
    }

    public onComputedPre(callback: (update: ComputedPreNotification) => void) {
        this.computedPreListeners.push(callback);
    }
}
