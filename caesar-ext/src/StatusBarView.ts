import * as vscode from "vscode";
import { VerificationStatus } from "./VerificationManager";
import { Manager, Observer } from "./Manager";
import { State, StateManager } from "./StateManager";


export class StatusBarView {

    private stateObserver: Observer;

    private statusBarItems: Array<vscode.StatusBarItem>;
    private progressText: vscode.StatusBarItem;

    constructor(stateManager: StateManager) {

        this.stateObserver = new Observer(stateManager, (update: State) => { this.receiveStateUpdate(update) });

        this.statusBarItems = [];

        this.progressText = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 99);
        this.progressText.text = "caesar";
        this.progressText.tooltip = "Caesar verification status";

        this.statusBarItems.push(this.progressText);

        this.showStatusBar();
    }

    public showStatusBar() {
        for (const statusBarItem of this.statusBarItems) {
            statusBarItem.show();
        }
    }

    public dispose() {
        for (const statusBarItem of this.statusBarItems) {
            statusBarItem.dispose();
        }
    }

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
