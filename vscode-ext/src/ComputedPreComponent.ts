import { Range, TextEditorDecorationType } from "vscode";
import * as vscode from 'vscode';
import { CONFIGURATION_SECTION, GutterInformationViewConfig, InlineGhostTextViewConfig } from "./Configuration";
import { ServerStatus } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";

export class ComputedPreComponent {

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
