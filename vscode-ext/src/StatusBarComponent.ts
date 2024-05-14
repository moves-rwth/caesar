import { StatusBarItem } from "vscode";
import * as vscode from 'vscode';
import { CONFIGURATION_SECTION, StatusBarViewConfig } from "./Configuration";
import { ServerStatus } from "./CaesarClient";
import { Verifier } from "./Verifier";
import { ConfigurationConstants } from "./constants";

export class StatusBarComponent {

    private enabled: boolean;
    private status: ServerStatus = ServerStatus.Stopped;
    private view: StatusBarItem;

    constructor(verifier: Verifier) {
        // create the view
        this.view = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 99);
        verifier.context.subscriptions.push(this.view);
        this.view.text = "Caesar";

        this.view.tooltip = new vscode.MarkdownString(
            "[Restart Caesar](command:caesar.restartServer)\n\n" +
            "[Start Caesar](command:caesar.startServer)\n\n" +
            "[Stop Caesar](command:caesar.stopServer)",
            true);

        // render if enabled
        this.enabled = StatusBarViewConfig.get(ConfigurationConstants.showStatusBar);
        this.render();

        // subscribe to config changes
        verifier.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (e.affectsConfiguration(StatusBarViewConfig.getFullPath(ConfigurationConstants.showStatusBar))) {
                this.enabled = StatusBarViewConfig.get(ConfigurationConstants.showStatusBar);
                this.render();
            }
        }));

        // listen to verifier updates
        verifier.client.onStatusUpdate((status) => {
            this.status = status;
            this.render();
        });
    }

    render() {
        if (this.enabled) {
            switch (this.status) {
                case ServerStatus.Stopped:
                    this.view.text = "$(debug-stop) Et tu, Brute?";
                    break;
                case ServerStatus.FailedToStart:
                    this.view.text = "$(warning) Failed to start Caesar";
                    break;
                case ServerStatus.Starting:
                    this.view.text = "$(sync~spin) Starting Caesar...";
                    break;
                case ServerStatus.Ready:
                    this.view.text = "$(check) Caesar Ready";
                    break;
                case ServerStatus.Verifying:
                    this.view.text = "$(sync~spin) Verifying...";
                    break;
                case ServerStatus.Finished:
                    this.view.text = "$(check) Verified";
                    break;
            }
            this.view.show();
        } else {
            this.view.hide();
        }
    }
}
