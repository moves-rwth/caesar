import * as vscode from 'vscode';

export abstract class EditorView {

    public abstract updateView(update: any): void;

    public abstract clearView(editor: vscode.TextEditor): void;

    public abstract dispose(): void;

    public clearVisibleEditors() {
        const editors = vscode.window.visibleTextEditors;
        editors.forEach(editor => this.clearView(editor));
    }

}
