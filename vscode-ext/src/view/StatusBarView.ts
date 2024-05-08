import * as vscode from "vscode";
import { VerificationStatus } from "../manager/VerificationManager";
import { Manager, Observer } from "../manager/Manager";
import { State, StateManager } from "../manager/StateManager";
import APIRegister from "../APIRegister";
import { CONFIGURATION_SECTION, StatusBarViewConfig } from "../Configuration";






/// The view for the status bar at the bottom of the editor
export class StatusBarView {

    private stateObserver: Observer;

    private statusBarItems: Array<vscode.StatusBarItem>;
    private progressText: vscode.StatusBarItem;

    constructor(stateManager: StateManager) {

        this.stateObserver = new Observer(stateManager, (update: State) => { this.receiveStateUpdate(update) });

        this.statusBarItems = [];

        this.progressText = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 99);
        this.progressText.text = "caesar";


        this.progressText.tooltip = new vscode.MarkdownString(
            "[Restart Caesar](command:caesar.restartServer)\n\n" +
            "[Start Caesar](command:caesar.startServer)\n\n" +
            "[Stop Caesar](command:caesar.stopServer)"
            , true);

        this.statusBarItems.push(this.progressText);

        this.showStatusBar();

        APIRegister.register("onDidChangeConfiguration", (e: vscode.ConfigurationChangeEvent) => {
            if (e.affectsConfiguration(CONFIGURATION_SECTION)) {
                if (StatusBarViewConfig.get("showStatusBar")) {
                    this.enable();
                } else {
                    this.disable();
                }
            }
        });

    }

    private showStatusBar() {
        for (const statusBarItem of this.statusBarItems) {
            statusBarItem.show();
        }
    }

    private hideStatusBar() {
        for (const statusBarItem of this.statusBarItems) {
            statusBarItem.hide();
        }
    }

    /// Disable the status bar by hiding it and disabling the observer
    public disable() {
        this.hideStatusBar();
        this.stateObserver.disable();
    }

    /// Enable the status bar by showing it and enabling the observer
    public enable() {
        this.showStatusBar();
        this.stateObserver.enable();
    }

    /// Dispose of the status bar
    public dispose() {
        for (const statusBarItem of this.statusBarItems) {
            statusBarItem.dispose();
        }
        this.stateObserver.disable();
    }

    /// Update the status bar text based on the latest state received from the StateManager
    private receiveStateUpdate(p: State) {
        switch (p) {
            case State.Starting:
                this.progressText.text = StatusBarText.Starting;
                break;
            case State.Ready:
                this.progressText.text = StatusBarText.Ready;
                break;
            case State.Verifying:
                this.progressText.text = StatusBarText.Verifying;
                break;
            case State.Finished:
                this.progressText.text = StatusBarText.Verified;
                break;
        }
    }

}


export enum StatusBarText {
    Starting = "$(sync~spin) Starting Caesar...",
    Ready = "$(check) Caesar Ready",
    Verifying = "$(sync~spin) Verifying...",
    Verified = "$(check) Verified"
}
