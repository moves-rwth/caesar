import { LanguageClientOptions, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Executable, LanguageClient, ServerOptions } from "vscode-languageclient/node";
import { ExtensionContext, OutputChannel, Range, TextDocument } from "vscode";
import * as vscode from "vscode";
import { ConfigurationConstants } from "./constants";
import { ServerConfig } from "./Configuration";
import * as path from "path";
import * as fs from 'fs';

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
    pres: [vscode.Range, string][];
}


export class CaesarClient {
    private outputChannel: OutputChannel;
    private client: LanguageClient | null = null;
    private context: ExtensionContext;
    private statusListeners = new Array<(status: ServerStatus) => void>();
    private updateListeners = new Array<(document: TextDocumentIdentifier, results: [Range, VerifyResult][]) => void>();
    private computedPreListeners = new Array<(document: TextDocumentIdentifier, results: [Range, string][]) => void>();

    constructor(context: ExtensionContext, outputChannel: OutputChannel) {
        this.context = context;
        this.outputChannel = outputChannel;

        // listen to commands
        vscode.commands.registerCommand('caesar.restartServer', async () => {
            await this.restart();
        });

        vscode.commands.registerCommand('caesar.startServer', async () => {
            await this.start();
        });

        vscode.commands.registerCommand('caesar.stopServer', async () => {
            await this.stop();
        });

        vscode.commands.registerCommand('caesar.verify', async () => {
            const openEditor = vscode.window.activeTextEditor;
            if (openEditor) {
                await this.verify(openEditor.document);
            }
        });

        vscode.commands.registerCommand('caesar.copyCommand', async () => {
            await this.copyCommand();
        });

        vscode.commands.registerCommand('caesar.showOutput', () => {
            this.client?.outputChannel.show();
        });

        this.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration(async (e: vscode.ConfigurationChangeEvent) => {
            if (e.affectsConfiguration(ServerConfig.getFullPath())) {
                console.log("Configuration changed");
                if (this.client !== null) {
                    await this.restart();
                }
            }
        }));
    }

    private createClient(context: vscode.ExtensionContext): LanguageClient {
        // Get the source code / binary path from the configurations
        const executable = this.getExecutable();
        const serverOptions: ServerOptions = {
            run: executable,
            debug: executable,
        };

        // Options to control the language client
        const clientOptions: LanguageClientOptions = {
            diagnosticCollectionName: 'caesar',
            // Register the server for heyvl documents
            documentSelector: [{ scheme: 'file', language: 'heyvl' }],
            synchronize: {
                // Notify the server about file changes to '.clientrc files contained in the workspace
                fileEvents: vscode.workspace.createFileSystemWatcher('**/*.heyvl')
            },
            outputChannel: this.outputChannel,
        };

        const client = new LanguageClient(
            'caesar',
            'Caesar',
            serverOptions,
            clientOptions
        );

        context.subscriptions.push(client);

        // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access
        client.info(`Starting Caesar for VSCode ${context.extension.packageJSON.version}.`);

        // set up listeners for our custom events
        context.subscriptions.push(client.onNotification("custom/verifyStatus", (params: VerifyStatusNotification) => {
            for (const listener of this.updateListeners) {
                listener(params.document, params.statuses);
            }
        }));

        context.subscriptions.push(client.onNotification("custom/computedPre", (params: ComputedPreNotification) => {
            for (const listener of this.computedPreListeners) {
                listener(params.document, params.pres);
            }
        }));

        // listen to onDidSaveTextDocument events
        context.subscriptions.push(vscode.workspace.onDidSaveTextDocument((document) => {
            // TODO: look at setting
            if (document.languageId !== "heyvl") {
                return;
            }
            void this.verify(document);
        }));

        return client;
    }

    private getExecutable(): Executable {
        let serverPath: string;
        let serverExecutable;
        const args: string[] = [];
        switch (ServerConfig.get(ConfigurationConstants.installationOptions)) {
            case ConfigurationConstants.binaryOption:
                serverPath = ServerConfig.get(ConfigurationConstants.binaryPath);
                if (serverPath === "") {
                    void vscode.window.showErrorMessage("Caesar: Binary path is not set. Please set the path in the settings.", "Open settings").then(async () => {
                        await vscode.commands.executeCommand('workbench.action.openSettings', 'caesar.server');
                    });
                    throw new Error("Installation path is not set");
                }
                serverExecutable = "caesar";
                args.push('--language-server');
                break;
            case ConfigurationConstants.sourceCodeOption:
                serverPath = ServerConfig.get(ConfigurationConstants.sourcePath);
                if (serverPath === "") {
                    void vscode.window.showErrorMessage("Caesar: Source path is not set. Please set the path in the settings.", "Open settings").then(async () => {
                        await vscode.commands.executeCommand('workbench.action.openSettings', 'caesar.server');
                    });
                    throw new Error("Installation path is not set");
                }
                if (!fs.existsSync(path.resolve(serverPath, "Cargo.toml"))) {
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

        const userArgs: string = ServerConfig.get(ConfigurationConstants.args);
        args.push(...userArgs.split(" "));
        const timeout: string = ServerConfig.get(ConfigurationConstants.timeout);
        // The timeout in args configuration overwrites the timeout configuration.
        if (userArgs.indexOf("--timeout") !== -1) {
            args.push("--timeout", timeout);
        }

        return {
            command: serverExecutable,
            args: args,
            options: {
                cwd: serverPath,
                env: {
                    ...process.env,
                    "NO_COLOR": "1",
                    "RUST_LOG": "caesar=info",
                    "RUST_BACKTRACE": "1"
                },
            }
        };
    }

    async start() {
        if (this.client !== null) {
            return;
        }

        console.log("Starting Caesar");
        this.notifyStatusUpdate(ServerStatus.Starting);

        try {
            this.client = this.createClient(this.context);
        } catch (error) {
            this.notifyStatusUpdate(ServerStatus.FailedToStart);
            void vscode.window.showErrorMessage("Failed to initialize Caesar");
            console.error(error);
            this.client = null;
        }

        await this.client!.start().catch((error: Error) => {
            console.error("Failed to start Caesar", error);
            void vscode.window.showErrorMessage("Failed to start Caesar:", error.message);
            this.notifyStatusUpdate(ServerStatus.FailedToStart);
        });
        this.notifyStatusUpdate(ServerStatus.Ready);
    }

    async restart() {
        await this.stop();
        await this.start();
    }

    async stop() {
        if (this.client === null) {
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
        if (this.client === null) {
            await this.start();
        }
        if (this.client === null) {
            return;
        }
        const documentItem = {
            uri: document.uri.toString(),
            languageId: document.languageId,
            version: document.version,
            text: document.getText()
        };
        this.notifyStatusUpdate(ServerStatus.Verifying);
        await this.client.sendRequest('custom/verify', { text_document: documentItem });
        // TODO: handle errors
        this.notifyStatusUpdate(ServerStatus.Finished);
    }

    private async copyCommand() {
        const executable = this.getExecutable();
        let line = `${executable.command} ${executable.args!.join(" ")}`;
        const cwd = executable.options && executable.options.cwd;
        if (cwd !== undefined) {
            line = `pushd ${cwd} && ${line}; popd`;
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

    public onComputedPre(callback: (document: TextDocumentIdentifier, results: [Range, string][]) => void) {
        this.computedPreListeners.push(callback);
    }
}
