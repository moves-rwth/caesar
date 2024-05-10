
import * as vscode from "vscode";
import { VerificationManager, VerificationStatus } from "../manager/VerificationManager";
import { Manager, Observer } from "../manager/Manager";
import Configuration, { CONFIGURATION_SECTION, ConfigCategory, GutterInformationViewConfig } from "../Configuration";
import APIRegister from "../APIRegister";
import { EditorView } from "./View";
import { VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { LanguageClient } from "vscode-languageclient/node";



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


/// The view that displays the verification status of individual (co)procedures in the gutter of the editor with corresponding icons
export class GutterInformationView extends EditorView {
    private enabled: boolean;
    private verificationObserver: Observer;

    private verifyDecType: vscode.TextEditorDecorationType;
    private failedDecType: vscode.TextEditorDecorationType;
    private unknownDecType: vscode.TextEditorDecorationType;

    private procStatus?: VerificationStatus;

    constructor(verificationManager: VerificationManager, context: vscode.ExtensionContext, client: LanguageClient) {
        super();

        this.enabled = GutterInformationViewConfig.get("showGutterIcons");

        this.verifyDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: context.asAbsolutePath('images/verified.png') });
        this.failedDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: context.asAbsolutePath('images/failed.png') });
        this.unknownDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: context.asAbsolutePath('images/unknown.png') });

        this.verificationObserver = new Observer(verificationManager, (update: VerificationStatus) => { this.receiveVerificationUpdate(update) });

        // Register the configuration change listener
        APIRegister.register("onDidChangeConfiguration", (e: vscode.ConfigurationChangeEvent) => {
            if (e.affectsConfiguration(CONFIGURATION_SECTION)) {
                console.log("Gutter Config Changed")
                if (GutterInformationViewConfig.get("showGutterIcons")) {
                    this.enable();
                } else {
                    this.disable();
                }
            }
        });

        client.onNotification("custom/verifyStatus", (params: VerificationStatus) => {
            this.receiveVerificationUpdate(params);
        })
    }

    /// Enable the GutterInformationView
    public enable() {
        if (this.enabled) {
            return;
        }
        this.enabled = true;
        this.verificationObserver.enable();
        this.updateView(vscode.window.activeTextEditor!)
    }

    /// Disable the GutterInformationView
    public disable() {
        if (!this.enabled) {
            return;
        }
        this.enabled = false;
        this.verificationObserver.disable();
        this.clearVisibleEditors()
    }

    /// Callback function for when the VerificationManager updates
    private receiveVerificationUpdate(newStatus: VerificationStatus) {
        // Update the decorations
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            this.procStatus = newStatus;
            this.updateView(editor);
        }
    }


    /// Clear the checkmarks from the given editor
    public clearView(editor: vscode.TextEditor) {
        editor.setDecorations(this.verifyDecType, []);
        editor.setDecorations(this.failedDecType, []);
        editor.setDecorations(this.unknownDecType, []);
    }

    /// Update the checkmarks based on the latest verification status received from the VerificationManager
    public updateView(editor: vscode.TextEditor) {
        const verifiedProcs: vscode.DecorationOptions[] = [];
        const failedProcs: vscode.DecorationOptions[] = [];
        const unknownProcs: vscode.DecorationOptions[] = [];
        if (this.enabled && this.procStatus != null && this.procStatus.document.uri == editor.document.uri.toString()) {
            for (const proc of this.procStatus.statuses) {
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
        }
        editor.setDecorations(this.verifyDecType, verifiedProcs);
        editor.setDecorations(this.failedDecType, failedProcs);
        editor.setDecorations(this.unknownDecType, unknownProcs);
    }


    /// Dispose of the GutterInformationView
    public dispose() {
        this.clearVisibleEditors();
        this.verificationObserver.disable();
        this.verifyDecType.dispose();
        this.failedDecType.dispose();
        this.unknownDecType.dispose();
    }

}



