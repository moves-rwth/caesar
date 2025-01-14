import { Range } from "vscode";
import * as vscode from 'vscode';
import { GutterInformationViewConfig } from "./Config";
import { ServerStatus, VerifyResult } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";
import { ConfigurationConstants } from "./constants";
import { TextDocumentIdentifier } from "vscode-languageclient";

export class GutterStatusComponent {

    private enabled: boolean;
    private status: DocumentMap<[Range, VerifyResult][]>;
    private registeredSourceUnits: DocumentMap<Range[]>;
    private serverStatus: ServerStatus = ServerStatus.NotStarted;

    private verifyDecType: vscode.TextEditorDecorationType;
    private failedDecType: vscode.TextEditorDecorationType;
    private unknownDecType: vscode.TextEditorDecorationType;

    constructor(verifier: Verifier) {
        // create decorations
        this.verifyDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath('images/verified.png') });
        this.failedDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath('images/failed.png') });
        this.unknownDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath('images/unknown.png') });

        // render if enabled
        this.enabled = GutterInformationViewConfig.get(ConfigurationConstants.showGutterIcons);

        this.status = new DocumentMap();
        this.registeredSourceUnits = new DocumentMap();

        // subscribe to config changes
        verifier.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (GutterInformationViewConfig.isAffected(e)) {
                this.enabled = GutterInformationViewConfig.get(ConfigurationConstants.showGutterIcons);
                this.render();
            }
        }));

        // render when visible editors change
        verifier.context.subscriptions.push(vscode.window.onDidChangeVisibleTextEditors(() => {
            this.render();
        }));

        // listen to status and verify updates
        verifier.client.onStatusUpdate((status) => {
            this.serverStatus = status;
            if (status === ServerStatus.Verifying) {
                for (const [_document, results] of this.status.entries()) {
                    results.length = 0;
                }
            }
            this.render();
        });

        verifier.client.onVerifyResult((document, results) => {
            this.status.insert(document, results);
            this.render();
        });

        verifier.client.onSourceUnitSpans((document, ranges) => {
            this.registeredSourceUnits.insert(document, ranges);
            this.render();
        });

        verifier.context.subscriptions.push(vscode.workspace.onDidCloseTextDocument((document) => {
            const documentIdentifier: TextDocumentIdentifier = { uri: document.uri.toString() };
            this.status.remove(documentIdentifier);
            this.registeredSourceUnits.remove(documentIdentifier);
            this.render();
        }));
    }

    render() {

        for (const editor of vscode.window.visibleTextEditors) {
            for (const [document_id, ranges] of this.registeredSourceUnits.entries()) {

                if (editor.document.uri.toString() !== document_id.uri) {
                    continue;
                }

                const verifiedProcs: vscode.DecorationOptions[] = [];
                const failedProcs: vscode.DecorationOptions[] = [];
                const unknownProcs: vscode.DecorationOptions[] = [];

                const results = this.status.get(document_id) || [];

                if (this.enabled) {
                    for (const range of ranges) {
                        const line = range.start.line;
                        const gutterRange = new vscode.Range(line, 0, line, 0);

                        // Try to find the result for the current registered range
                        const index = results.findIndex((value) => value[0].start.line === line);
                        console.log(index);
                        if (index === -1) {
                            if (this.serverStatus === ServerStatus.Ready) {
                                // If the result is not found, we assume it is unknown
                                unknownProcs.push({ range: gutterRange, hoverMessage: 'Unknown' });
                            }
                        } else {
                            // If the result is found, we check its status and display the appropriate icon
                            switch (results[index][1]) {
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
                }

                editor.setDecorations(this.verifyDecType, verifiedProcs);
                editor.setDecorations(this.failedDecType, failedProcs);
                editor.setDecorations(this.unknownDecType, unknownProcs);
            }
        }
    }
}
