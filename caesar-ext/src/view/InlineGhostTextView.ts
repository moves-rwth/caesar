import * as vscode from "vscode";
import { Observer } from "../manager/Manager";
import { VerificationManager, VerificationStatus } from "../manager/VerificationManager";
import APIRegister from "../APIRegister";
import { CONFIGURATION_SECTION, InlineGhostTextViewConfig } from "../Configuration";
import { EditorView } from "./View";


/// The view that shows the wp/wrt/ert of the respective lines as ghost text in the editor
export class InlineGhostTextView extends EditorView {

    private verificationObserver: Observer;


    private lineTextMap: Map<number, string> = new Map([[1, "test"], [2, "test2"], [3, "test3"]]);

    private decorationType: vscode.TextEditorDecorationType;

    constructor(verificationManager: VerificationManager) {
        super();
        this.verificationObserver = new Observer(verificationManager, (update: VerificationStatus) => { this.receiveVerificationUpdate(update) });
        this.decorationType = vscode.window.createTextEditorDecorationType({});


        APIRegister.register("onDidChangeConfiguration", (e: vscode.ConfigurationChangeEvent) => {
            if (e.affectsConfiguration(CONFIGURATION_SECTION)) {
                if (InlineGhostTextViewConfig.get("showInlineGhostText")) {
                    this.enable();
                } else {
                    this.disable();
                }
            }
        });

    }

    public enable() {
        this.verificationObserver.enable();
        this.updateView(vscode.window.activeTextEditor!);
    }

    public disable() {
        this.verificationObserver.disable();
        this.clearVisibleEditors();
    }

    private receiveVerificationUpdate(newStatus: VerificationStatus) {
        // Update the decorations
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.updateView(editor);
        }
    }

    public updateText(line: number, text: string) {
        this.lineTextMap.set(line, text);
    }

    public clearView(editor: vscode.TextEditor) {
        editor.setDecorations(this.decorationType, []);
    }

    public updateView(editor: vscode.TextEditor) {
        const decorations: vscode.DecorationOptions[] = [];

        this.lineTextMap.forEach((text, line) => {
            if (this.checkEmptyLine(Math.max(0, line - 1))) {
                const range = new vscode.Range(Math.max(0, line - 1), 0, Math.max(0, line - 1), 0);
                decorations.push({
                    range, renderOptions: {
                        after: {
                            backgroundColor: new vscode.ThemeColor('caesar.inlineGhostBackgroundColor'),
                            color: new vscode.ThemeColor('caesar.inlineGhostForegroundColor'),
                            contentText: text
                        }
                    }
                });
            }
        });

        editor.setDecorations(this.decorationType, decorations);
    }

    public checkEmptyLine(line: number): boolean {
        // Checks if the line above the given line number is empty
        const textEditor = vscode.window.activeTextEditor;
        if (textEditor && textEditor.document.lineCount > line) {
            const lineText = textEditor.document.lineAt(line).text;
            return lineText.trim() === '';
        }
        return false;
    }

    public dispose() {
        this.clearVisibleEditors();
        this.decorationType.dispose();
    }

}
