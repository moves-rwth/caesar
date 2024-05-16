import { MarkdownString, Range, TextEditorDecorationType } from "vscode";
import * as vscode from 'vscode';
import { InlineGhostTextViewConfig } from "./Configuration";
import { ServerStatus } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";
import { ConfigurationConstants } from "./constants";

export class ComputedPreComponent {

    private enabled: boolean;
    private computedPres: DocumentMap<[Range, boolean, [string, string][]][]>;

    private decorationType: TextEditorDecorationType;

    constructor(verifier: Verifier) {
        // create decoration
        const backgroundColor = new vscode.ThemeColor('caesar.inlineGhostBackgroundColor');
        const color = new vscode.ThemeColor('caesar.inlineGhostForegroundColor');
        this.decorationType = vscode.window.createTextEditorDecorationType({
            after: {
                backgroundColor,
                color,
                fontStyle: "italic",
            }
        });

        // set enabled flag
        this.enabled = InlineGhostTextViewConfig.get(ConfigurationConstants.showInlineGhostText);

        this.computedPres = new DocumentMap();

        // subscribe to config changes
        verifier.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (e.affectsConfiguration(InlineGhostTextViewConfig.getFullPath(ConfigurationConstants.showInlineGhostText))) {
                this.enabled = InlineGhostTextViewConfig.get(ConfigurationConstants.showInlineGhostText);
                this.render();
            }
        }));

        // render when visible text editors change
        verifier.context.subscriptions.push(vscode.window.onDidChangeVisibleTextEditors(() => {
            this.render();
        }));

        // render when the content is changed
        verifier.context.subscriptions.push(vscode.workspace.onDidChangeTextDocument((event) => {
            const uri = event.document.uri.toString();
            if (event.document.languageId === "heyvl" && this.computedPres.get({ uri }) !== undefined) {
                this.computedPres.insert({ uri }, []);
                this.render();
            }
        }));

        // listen to custom/computedPre notifications
        verifier.client.onComputedPre((update) => {
            this.computedPres.insert(update.document, update.pres);
            this.render();
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
        for (const [document_id, expr_expls] of this.computedPres.entries()) {
            for (const editor of vscode.window.visibleTextEditors) {
                if (editor.document.uri.toString() !== document_id.uri) {
                    continue;
                }

                const decorations: vscode.DecorationOptions[] = [];

                if (this.enabled) {
                    let prevLine;

                    for (const [range, isBlockItself, expls] of expr_expls) {
                        const line = range.start.line;
                        if (line === prevLine) {
                            break;
                        }
                        prevLine = line;

                        // how many lines are empty above the span?
                        let freeLines = 0;
                        // eslint-disable-next-line no-constant-condition
                        while (true) {
                            const checkLine = line - freeLines - 1;
                            if (freeLines === expls.length || checkLine < 0 || editor.document.lineAt(checkLine).text.trim() !== '') {
                                break;
                            }
                            freeLines++;
                        }

                        const expls_to_show = [...expls];
                        expls_to_show.splice(0, expls.length - freeLines);

                        for (const [index, [expl_one_line, expl_hover]] of expls_to_show.entries()) {
                            const lineAbove = line - index - 1;
                            const rangeAbove = new vscode.Range(lineAbove, 0, lineAbove, 0);
                            let col = range.start.character;
                            if (isBlockItself) {
                                col += 4;
                            }
                            // insert padding with em space unicode character
                            // because actual spaces will be trimmed by vscode
                            const contentText = "\u2003".repeat(col) + "▷ " + expl_one_line; // other options: ❯, ▷, ⟫, ⦊
                            const hoverMessage = new MarkdownString("```heyvl\n" + expl_hover + "\n```");
                            decorations.push({
                                hoverMessage,
                                range: rangeAbove,
                                renderOptions: {
                                    after: {
                                        contentText,
                                    },
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
