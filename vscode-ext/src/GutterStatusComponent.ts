import { Range } from "vscode";
import * as vscode from 'vscode';
import { CONFIGURATION_SECTION, GutterInformationViewConfig, StatusBarViewConfig } from "./Configuration";
import { ServerStatus, VerifyResult } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";

export class GutterStatusComponent {

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
                this.enabled = GutterInformationViewConfig.get("showGutterIcons");
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
