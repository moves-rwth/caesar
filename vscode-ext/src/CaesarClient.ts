import { LanguageClientOptions, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { LanguageClient, ServerOptions } from "vscode-languageclient/node";
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

export type VerifyStatusNotification = {
    document: VersionedTextDocumentIdentifier;
    statuses: Array<[vscode.Range, VerifyResult]>;
};

export type ComputedPreNotification = {
    document: VersionedTextDocumentIdentifier;
    pres: Array<[vscode.Range, string]>;
};


export class CaesarClient {
    private client: LanguageClient | null;
    private context: ExtensionContext;
    private statusListeners: Array<(status: ServerStatus) => void> = new Array();
    private updateListeners: Array<(document: TextDocumentIdentifier, results: Array<[Range, VerifyResult]>) => void> = new Array();
    private computedPreListeners: Array<(document: TextDocumentIdentifier, results: Array<[Range, string]>) => void> = new Array();


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
    }

    /// Try to initialize the client and return the client if successful otherwise return null
    private initialize(context: ExtensionContext): LanguageClient | null {
        try {
            this.client = this.createClient(context);
        } catch (error) {
            this.notifyStatusUpdate(ServerStatus.FailedToStart);
            vscode.window.showErrorMessage("Failed to initialize Caesar")
            console.error(error)
            this.client = null;
        }

        return this.client;
    }

    private createClient(context: vscode.ExtensionContext): LanguageClient {
        // Get the source code / binary path from the configurations
        let serverPath: string = ServerConfig.get(ConfigurationConstants.installationPath);
        if (serverPath === "") {
            vscode.window.showErrorMessage("Caesar: Installation path is not set. Please set the path in the settings.")
            throw new Error("Installation path is not set")
        }
        let serverExecutable = "";
        let args: string[] = [];
        switch (ServerConfig.get(ConfigurationConstants.installationOptions)) {
            case ConfigurationConstants.binaryOption:
                serverExecutable = "caesar";
                args = ['--language-server'];
                break;
            case ConfigurationConstants.sourceCodeOption:
                if (!fs.existsSync(path.resolve(serverPath, "Cargo.toml"))) {
                    vscode.window.showErrorMessage("Caesar: Cargo.toml file is not found in the path. Please check the path in the settings.")
                    throw new Error("Cargo.toml file is not found in the path")
                }
                serverExecutable = "cargo";
                args = ['run', '--', '--language-server'];
                break;
        }

        // If the extension is launched in debug mode then the debug server options are used
        // Otherwise the run options are used
        let serverOptions: ServerOptions = {
            run: {
                command: serverExecutable,
                args: args,
                options: {
                    cwd: serverPath,
                }
            },
            debug: {
                command: serverExecutable,
                args: args,
                options: {
                    cwd: serverPath,
                    env: {
                        ...process.env,
                        "NO_COLOR": "1",
                        "RUST_BACKTRACE": "1"
                    }
                }
            }
        };

        // Options to control the language client
        let clientOptions: LanguageClientOptions = {
            diagnosticCollectionName: 'caesar',
            // Register the server for heyvl documents
            documentSelector: [{ scheme: 'file', language: 'heyvl' }],
            synchronize: {
                // Notify the server about file changes to '.clientrc files contained in the workspace
                fileEvents: vscode.workspace.createFileSystemWatcher('**/*.heyvl')
            }
        };

        let client = new LanguageClient(
            'caesar',
            'Caesar',
            serverOptions,
            clientOptions
        );

        context.subscriptions.push(client)

        // set up listeners for our custom events
        context.subscriptions.push(client.onNotification("custom/verifyStatus", (params: VerifyStatusNotification) => {
            for (let listener of this.updateListeners) {
                listener(params.document, params.statuses);
            }
        }));

        context.subscriptions.push(client.onNotification("custom/computedPre", (params: ComputedPreNotification) => {
            for (let listener of this.computedPreListeners) {
                listener(params.document, params.pres);
            }
        }));

        // listen to onDidSaveTextDocument events
        context.subscriptions.push(vscode.workspace.onDidSaveTextDocument((document) => {
            // TODO: look at setting
            if (document.languageId !== "heyvl") {
                return
            }
            this.verify(document);
        }));

        vscode.commands.registerCommand('caesar.verify', async () => {
            let openEditor = vscode.window.activeTextEditor;
            if (openEditor) {
                this.verify(openEditor.document);
            }
        });
        return client;
    }

    async start() {
        console.log("Starting Caesar");
        this.notifyStatusUpdate(ServerStatus.Starting);
        // If the client is null, try initializing it and if it also fails show an error message
        if (this.client === null) {
            // First initialize the client by creating a new one, if it fails return
            if (this.initialize(this.context) === null) {
                return
            };
        }
        await this.client!.start();
        this.notifyStatusUpdate(ServerStatus.Ready);

    }

    async restart() {
        if (this.client === null) {
            this.start()
            return
        } else {
            console.log("Restarting Caesar");
            this.client?.restart();
        }
    }

    async stop() {
        console.log("Stopping Caesar");
        this.client?.stop();
        this.notifyStatusUpdate(ServerStatus.Stopped);
    }

    async verify(document: TextDocument) {
        if (this.client === null) {
            return
        }
        let documentItem = {
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

    public onStatusUpdate(callback: (status: ServerStatus) => void) {
        this.statusListeners.push(callback);
    }

    private notifyStatusUpdate(status: ServerStatus) {
        for (let listener of this.statusListeners) {
            listener(status);
        }
    }

    public onVerifyResult(callback: (document: TextDocumentIdentifier, results: Array<[Range, VerifyResult]>) => void) {
        this.updateListeners.push(callback);
    }

    public onComputedPre(callback: (document: TextDocumentIdentifier, results: Array<[Range, string]>) => void) {
        this.computedPreListeners.push(callback);
    }
}
