import { LanguageClientOptions, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { LanguageClient, ServerOptions } from "vscode-languageclient/node";
import { ExtensionContext, Range, TextDocument } from "vscode";
import * as vscode from "vscode";

export enum ServerStatus {
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
    private client: LanguageClient;
    private statusListeners: Array<(status: ServerStatus) => void> = new Array();
    private updateListeners: Array<(document: TextDocumentIdentifier, results: Array<[Range, VerifyResult]>) => void> = new Array();
    private computedPreListeners: Array<(document: TextDocumentIdentifier, results: Array<[Range, string]>) => void> = new Array();

    constructor(context: ExtensionContext) {
        let serverOptions: ServerOptions = {
            run: {
                command: 'cargo',
                args: ['run', '--', '--language-server'],
                options: {

                }, // TODO!!
            },
            debug: {
                command: 'cargo',
                args: ['run', '--', '--language-server'],
                options: {

                    env: {
                        ...process.env,
                        "RUST_LOG": "caesar=info",
                        "NO_COLOR": "1",
                        "RUST_BACKTRACE": "1"
                    }
                }, // TODO!!
            }
        };

        let clientOptions: LanguageClientOptions = {
            diagnosticCollectionName: 'caesar',
            documentSelector: [{ scheme: 'file', language: 'heyvl' }],
            synchronize: {
                // Notify the server about file changes to '.clientrc files contained in the workspace
                fileEvents: vscode.workspace.createFileSystemWatcher('**/*.heyvl')
            }
        };

        // Create the language client and start the client.
        this.client = new LanguageClient(
            'caesar',
            'Caesar',
            serverOptions,
            clientOptions
        );
        context.subscriptions.push(this.client);

        // set up listeners for our custom events
        context.subscriptions.push(this.client.onNotification("custom/verifyStatus", (params: VerifyStatusNotification) => {
            for (let listener of this.updateListeners) {
                listener(params.document, params.statuses);
            }
        }));

        context.subscriptions.push(this.client.onNotification("custom/computedPre", (params: ComputedPreNotification) => {
            for (let listener of this.computedPreListeners) {
                listener(params.document, params.pres);
            }
        }));

        // listen to onDidSaveTextDocument events
        context.subscriptions.push(vscode.workspace.onDidSaveTextDocument((document) => {
            // TODO: look at setting
            this.verify(document);
        }));

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
            let openEditor = vscode.window.activeTextEditor;
            if (openEditor) {
                this.verify(openEditor.document);
            }
        });
    }

    async start() {
        console.log("Starting Caesar");
        this.notifyStatusUpdate(ServerStatus.Starting);
        await this.client.start();
        this.notifyStatusUpdate(ServerStatus.Ready);
    }

    async restart() {
        console.log("Restarting Caesar");
        this.client.restart();
    }

    async stop() {
        console.log("Stopping Caesar");
        this.client.stop();
    }

    async verify(document: TextDocument) {
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