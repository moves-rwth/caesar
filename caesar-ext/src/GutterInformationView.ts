
import * as vscode from "vscode";
import { VerificationManager, VerificationStatus } from "./VerificationManager";
import { Manager, Observer } from "./Manager";


export enum VerifyStatus {
    Verified,
    Failed,
    Unknown
}

export enum VerificationColors {
    Verified = '#66f542',
    Failed = '#f23a3a',
    Unknown = '#f7aa57'
}


export class GutterInformationView {
    private verificationObserver: Observer;

    private verifyDecType: vscode.TextEditorDecorationType;
    private failedDecType: vscode.TextEditorDecorationType;
    private unknownDecType: vscode.TextEditorDecorationType;

    constructor(verificationManager: VerificationManager, context: vscode.ExtensionContext) {

        this.verificationObserver = new Observer(verificationManager, (update: VerificationStatus) => { this.receiveVerificationUpdate(update) });
        this.verifyDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: context.asAbsolutePath('images/verified.png') });
        this.failedDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: context.asAbsolutePath('images/failed.png') });
        this.unknownDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: context.asAbsolutePath('images/unknown.png') });
    }

    private receiveVerificationUpdate(newStatus: VerificationStatus) {
        // Update the decorations
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.updateDecorations(editor, newStatus);
        }
    }


    private updateDecorations(editor: vscode.TextEditor, procStatus: VerificationStatus = []) {
        const verifiedProcs: vscode.DecorationOptions[] = [];
        const failedProcs: vscode.DecorationOptions[] = [];
        const unknownProcs: vscode.DecorationOptions[] = [];

        for (const proc of procStatus) {
            const verified = proc[1];

            const line = proc[0].start.line;
            const range = new vscode.Range(line, 0, line, 0);
            if (verified) {
                // Put the checkmark before the proc.
                verifiedProcs.push({ range, hoverMessage: 'Verified' });
            } else {
                // Put the X before the proc.
                failedProcs.push({ range, hoverMessage: 'Not Verified' });
            }
        }
        editor.setDecorations(this.verifyDecType, verifiedProcs);
        editor.setDecorations(this.failedDecType, failedProcs);
        editor.setDecorations(this.unknownDecType, unknownProcs);
    }


    public dispose() {
        this.verifyDecType.dispose();
        this.failedDecType.dispose();
        this.unknownDecType.dispose();
    }

}



