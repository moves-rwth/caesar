import { Range, TextEditorDecorationType } from "vscode";
import * as vscode from 'vscode';
import { CONFIGURATION_SECTION, GutterInformationViewConfig, InlineGhostTextViewConfig } from "./Configuration";
import { ServerStatus } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";

export class ComputedPreComponent {

    private enabled: boolean;
    private computedPres: DocumentMap<[Range, string][]>;

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
        verifier.context.subscriptions.push(vscode.window.onDidChangeVisibleTextEditors(() => {
            this.render();
        }));

        // listen to custom/computedPre notifications
        verifier.client.onComputedPre((document, pres) => {
            this.computedPres.insert(document, pres);
        });

        // clear all information when a new verification task is started
        verifier.client.onStatusUpdate((status) => {
            if (status === ServerStatus.Verifying) {
                for (const [_document, results] of this.computedPres.entries()) {
                    results.length = 0;
                }
                this.render();
            }
        });

        // TODO: listen to content changes to remove lines?
    }

    render() {
        const backgroundColor = new vscode.ThemeColor('caesar.inlineGhostBackgroundColor');
        const color = new vscode.ThemeColor('caesar.inlineGhostForegroundColor');

        for (const [document_id, pres] of this.computedPres.entries()) {
            for (const editor of vscode.window.visibleTextEditors) {
                if (editor.document.uri.toString() !== document_id.uri) {
                    continue;
                }

                const decorations: vscode.DecorationOptions[] = [];

                if (this.enabled) {
                    for (const [range, text] of pres) {
                        const line = range.start.line;
                        if (line === 0) {
                            continue;
                        }
                        const lineAbove = line - 1;
                        const rangeAbove = new vscode.Range(lineAbove, 0, lineAbove, 0);
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
