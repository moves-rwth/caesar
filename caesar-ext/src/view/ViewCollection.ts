import * as vscode from "vscode";

import { StateManager } from "../manager/StateManager";
import { VerificationManager } from "../manager/VerificationManager";
import { GutterInformationView } from "./GutterInformationView";
import { InlineGhostTextView } from "./InlineGhostTextView";
import { StatusBarView } from "./StatusBarView";


/// A container for all the views in the extension
/// Manages the creation and the on/off configurations of the views
export class ViewCollection {
    public gutterInfo: GutterInformationView | null;
    public statusBar: StatusBarView | null;
    public inlineGhostText: InlineGhostTextView | null;


    constructor(verificationManager: VerificationManager, stateManager: StateManager, context: vscode.ExtensionContext) {
        this.gutterInfo = new GutterInformationView(verificationManager, context);
        this.statusBar = new StatusBarView(stateManager);
        this.inlineGhostText = new InlineGhostTextView(verificationManager);
    }

    public dispose() {
        this.gutterInfo?.dispose();
        this.statusBar?.dispose();
        this.inlineGhostText?.dispose();
    }

}
