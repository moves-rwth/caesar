import { LanguageClientOptions, TextDocumentIdentifier, VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { LanguageClient, ServerOptions } from "vscode-languageclient/node";
import { ExtensionContext, Range, StatusBarItem, TextDocument, TextEditorDecorationType } from "vscode";
import * as vscode from 'vscode';
import { CONFIGURATION_SECTION, GutterInformationViewConfig, InlineGhostTextViewConfig, StatusBarViewConfig } from "./Configuration";

class DocumentMap<T> {
    private map: Map<string, [TextDocumentIdentifier, T]> = new Map();

    public insert(document_id: TextDocumentIdentifier, value: T) {
        this.map.set(document_id.uri.toString(), [document_id, value]);
    }

    public get(document_id: TextDocumentIdentifier): T | undefined {
        let res = this.map.get(document_id.uri.toString());
        if (res !== undefined) {
            return res[1];
        }
        return undefined;
    }

    public entries(): Array<[TextDocumentIdentifier, T]> {
        return Array.from(this.map.values());
    }
}

export enum ServerStatus {
    Starting,
    Ready,
    FailedToStart,
    Verifying,
    Finished,
}

export enum VerifyResult {
    Verified = "verified",
    Failed = "failed",
    Unknown = "unknown",
}

export type VerifyStatusNotification = {
    document: VersionedTextDocumentIdentifier,
    statuses: Array<[vscode.Range, VerifyResult]>,
};

export type ComputedPreNotification = {
    document: VersionedTextDocumentIdentifier,
    pres: Array<[vscode.Range, string]>,
};

class CaesarClient {
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

export class Verifier {

    public context: ExtensionContext;
    public client: CaesarClient;
    private statusBar: StatusBarComponent;
    private gutterStatus: GutterStatusComponent;
    private displayComputedPre: ComputedPreComponent;

    constructor(context: ExtensionContext) {
        this.context = context;
        this.client = new CaesarClient(context);
        this.statusBar = new StatusBarComponent(this);
        this.gutterStatus = new GutterStatusComponent(this);
        this.displayComputedPre = new ComputedPreComponent(this);
    }

    async start() {
        await this.client.start();
    }

}

class StatusBarComponent {

    private enabled: boolean;
    private status: ServerStatus = ServerStatus.Starting;
    private view: StatusBarItem;

    constructor(verifier: Verifier) {
        // create the view
        this.view = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 99);
        verifier.context.subscriptions.push(this.view);
        this.view.text = "Caesar";

        this.view.tooltip = new vscode.MarkdownString(
            "[Restart Caesar](command:caesar.restartServer)\n\n" +
            "[Start Caesar](command:caesar.startServer)\n\n" +
            "[Stop Caesar](command:caesar.stopServer)"
            , true);

        // render if enabled
        this.enabled = StatusBarViewConfig.get("showStatusBar");
        this.render();

        // subscribe to config changes
        verifier.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (e.affectsConfiguration(CONFIGURATION_SECTION)) {
                this.enabled = StatusBarViewConfig.get("showStatusBar");
                this.render();
            }
        }));

        // listen to verifier updates
        verifier.client.onStatusUpdate((status) => {
            this.status = status;
            this.render();
        });
    }

    render() {
        if (this.enabled) {
            switch (this.status) {
                case ServerStatus.Starting:
                    this.view.text = "$(sync~spin) Starting Caesar...";
                    break;
                case ServerStatus.Ready:
                    this.view.text = "$(check) Caesar Ready";
                    break;
                case ServerStatus.Verifying:
                    this.view.text = "$(sync~spin) Verifying...";
                    break;
                case ServerStatus.Finished:
                    this.view.text = "$(check) Verified";
                    break;
            }
            this.view.show();
        } else {
            this.view.hide();
        }
    }
}

class GutterStatusComponent {

    private enabled: boolean;
    private status: DocumentMap<Array<[Range, VerifyResult]>>;

    private verifyDecType: vscode.TextEditorDecorationType;
    private failedDecType: vscode.TextEditorDecorationType;
    private unknownDecType: vscode.TextEditorDecorationType;

    constructor(verifier: Verifier) {
        // create decorations
        this.verifyDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath('images/verified.png') });
        this.failedDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath('images/failed.png') });
        this.unknownDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath('images/unknown.png') });

        // render if enabled
        this.enabled = GutterInformationViewConfig.get("showGutterIcons");

        this.status = new DocumentMap();

        // subscribe to config changes
        verifier.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (e.affectsConfiguration(CONFIGURATION_SECTION)) {
                this.enabled = StatusBarViewConfig.get("showGutterIcons");
                this.render();
            }
        }));

        // render when visible editors change
        verifier.context.subscriptions.push(vscode.window.onDidChangeVisibleTextEditors((_visibleEditors) => {
            this.render();
        }));

        // listen to status and verify updates
        verifier.client.onStatusUpdate((status) => {
            if (status == ServerStatus.Verifying) {
                for (let [_document, results] of this.status.entries()) {
                    results.length = 0;
                }
                this.render();
            }
        });

        verifier.client.onVerifyResult((document, results) => {
            this.status.insert(document, results);
            this.render();
        });
    }

    render() {
        for (let [document_id, results] of this.status.entries()) {
            for (let editor of vscode.window.visibleTextEditors) {
                if (editor.document.uri.toString() !== document_id.uri) {
                    continue;
                }

                let verifiedProcs: vscode.DecorationOptions[] = [];
                let failedProcs: vscode.DecorationOptions[] = [];
                let unknownProcs: vscode.DecorationOptions[] = [];

                if (this.enabled) {
                    for (let [range, result] of results) {
                        let line = range.start.line;
                        let gutterRange = new vscode.Range(line, 0, line, 0);
                        switch (result) {
                            case VerifyResult.Verified:
                                verifiedProcs.push({ range: gutterRange, hoverMessage: 'Verified' });
                                break;
                            case VerifyResult.Failed:
                                failedProcs.push({ range: gutterRange, hoverMessage: 'Not Verified' });
                                break;
                            case VerifyResult.Unknown:
                                unknownProcs.push({ range: gutterRange, hoverMessage: 'Unknown' });
                                break;
                        }
                    }
                }

                editor.setDecorations(this.verifyDecType, verifiedProcs);
                editor.setDecorations(this.failedDecType, failedProcs);
                editor.setDecorations(this.unknownDecType, unknownProcs);
            }
        }
    }
}

class ComputedPreComponent {

    private enabled: boolean;
    private computedPres: DocumentMap<Array<[Range, string]>>;

    private decorationType: TextEditorDecorationType;

    constructor(verifier: Verifier) {
        // create decoration
        this.decorationType = vscode.window.createTextEditorDecorationType({});

        // set enabled flag
        this.enabled = GutterInformationViewConfig.get("showGutterIcons");

        this.computedPres = new DocumentMap();

        // subscribe to config changes
        verifier.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (e.affectsConfiguration(CONFIGURATION_SECTION)) {
                this.enabled = InlineGhostTextViewConfig.get("showInlineGhostText");
                this.render();
            }
        }));

        // render when visible text editors change
        verifier.context.subscriptions.push(vscode.window.onDidChangeVisibleTextEditors((_visibleEditors) => {
            this.render();
        }));

        // listen to custom/computedPre notifications
        verifier.client.onComputedPre((document, pres) => {
            this.computedPres.insert(document, pres);
        });

        // clear all information when a new verification task is started
        verifier.client.onStatusUpdate((status) => {
            if (status == ServerStatus.Verifying) {
                for (let [_document, results] of this.computedPres.entries()) {
                    results.length = 0;
                }
                this.render();
            }
        });

        // TODO: listen to content changes to remove lines?
    }

    render() {
        let backgroundColor = new vscode.ThemeColor('caesar.inlineGhostBackgroundColor');
        let color = new vscode.ThemeColor('caesar.inlineGhostForegroundColor');

        for (let [document_id, pres] of this.computedPres.entries()) {
            for (let editor of vscode.window.visibleTextEditors) {
                if (editor.document.uri.toString() !== document_id.uri) {
                    continue;
                }

                let decorations: vscode.DecorationOptions[] = [];

                if (this.enabled) {
                    for (let [range, text] of pres) {
                        let line = range.start.line;
                        if (line === 0) {
                            continue;
                        }
                        let lineAbove = line - 1;
                        let rangeAbove = new vscode.Range(lineAbove, 0, lineAbove, 0);
                        if (editor.document.lineAt(lineAbove).text.trim() === '') {
                            decorations.push({
                                range: rangeAbove,
                                renderOptions: {
                                    after: {
                                        backgroundColor,
                                        color,
                                        contentText: text
                                    }
                                }
                            });
                        }
                    }
                }

                editor.setDecorations(this.decorationType, decorations);
            }
        }
    }
}
