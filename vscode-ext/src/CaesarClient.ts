import { LanguageClientOptions, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Executable, LanguageClient, ServerOptions } from "vscode-languageclient/node";
import { ExtensionContext, Range, TextDocument } from "vscode";
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
    private client: LanguageClient | null;
    private context: ExtensionContext;
    private statusListeners = new Array<(status: ServerStatus) => void>();
    private updateListeners = new Array<(document: TextDocumentIdentifier, results: [Range, VerifyResult][]) => void>();
    private computedPreListeners = new Array<(document: TextDocumentIdentifier, results: [Range, string][]) => void>();


    constructor(context: ExtensionContext) {
        this.context = context;
        // Initialize and start the server if the autoStartServer configuration is set otherwise set the client to null
        this.client = this.initialize(context);

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

        vscode.commands.registerCommand('caesar.copyCommand', async () => {
            await this.copyCommand();
        });

        vscode.commands.registerCommand('caesar.showOutput', () => {
            this.client?.outputChannel.show();
        });
    }

    /// Try to initialize the client and return the client if successful otherwise return null
    private initialize(context: ExtensionContext): LanguageClient | null {
        try {
            this.client = this.createClient(context);
        } catch (error) {
            this.notifyStatusUpdate(ServerStatus.FailedToStart);
            void vscode.window.showErrorMessage("Failed to initialize Caesar");
            console.error(error);
            this.client = null;
        }

        return this.client;
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

        vscode.commands.registerCommand('caesar.verify', async () => {
            const openEditor = vscode.window.activeTextEditor;
            if (openEditor) {
                await this.verify(openEditor.document);
            }
        });
        return client;
    }

    private getExecutable(): Executable {
        const serverPath: string = ServerConfig.get(ConfigurationConstants.installationPath);
        if (serverPath === "") {
            void vscode.window.showErrorMessage("Caesar: Installation path is not set. Please set the path in the settings.");
            throw new Error("Installation path is not set");
        }
        let serverExecutable;
        const args: string[] = [];
        switch (ServerConfig.get(ConfigurationConstants.installationOptions)) {
            case ConfigurationConstants.binaryOption:
                serverExecutable = "caesar";
                args.push('--language-server');
                break;
            case ConfigurationConstants.sourceCodeOption:
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
        console.log("Starting Caesar");
        this.notifyStatusUpdate(ServerStatus.Starting);
        // If the client is null, try initializing it and if it also fails show an error message
        if (this.client === null) {
            // First initialize the client by creating a new one, if it fails return
            if (this.initialize(this.context) === null) {
                return;
            };
        }
        await this.client!.start();
        this.notifyStatusUpdate(ServerStatus.Ready);

    }

    async restart() {
        if (this.client === null) {
            await this.start();
        } else {
            console.log("Restarting Caesar");
            await this.client?.restart();
        }
    }

    async stop() {
        console.log("Stopping Caesar");
        await this.client?.stop();
        this.notifyStatusUpdate(ServerStatus.Stopped);
    }

    async verify(document: TextDocument) {
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
