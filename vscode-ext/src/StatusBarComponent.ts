import { StatusBarItem, Range } from "vscode";
import * as vscode from 'vscode';
import { StatusBarViewConfig } from "./Config";
import { ServerStatus, VerifyResult } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";
import { ConfigurationConstants } from "./constants";

export class StatusBarComponent {

    private enabled: boolean;
    private verifyStatus: DocumentMap<[Range, VerifyResult][]> = new DocumentMap();
    private serverStatus: ServerStatus = ServerStatus.NotStarted;
    private view: StatusBarItem;

    constructor(verifier: Verifier) {
        // create the view
        this.view = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 99);
        verifier.context.subscriptions.push(this.view);
        this.view.text = "Caesar";
        this.view.command = "caesar.showOutput";

        this.view.tooltip = new vscode.MarkdownString(
            "<a href='command:caesar.restartServer'>Restart Caesar</a>\n\n" +
            "[Start Caesar](command:caesar.startServer)\n\n" +
            "[Stop Caesar](command:caesar.stopServer)",
            true);

        // render if enabled
        this.enabled = StatusBarViewConfig.get(ConfigurationConstants.showStatusBar);
        this.render();

        // subscribe to config changes
        verifier.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (StatusBarViewConfig.isAffected(e)) {
                this.enabled = StatusBarViewConfig.get(ConfigurationConstants.showStatusBar);
                this.render();
            }
        }));

        // listen to verifier updates
        verifier.client.onStatusUpdate((status) => {
            this.serverStatus = status;
            this.render();
        });

        verifier.client.onVerifyResult((document, results) => {
            this.verifyStatus.insert(document, results);
            this.render();
        });

    }

    render() {
        if (this.enabled) {
            switch (this.serverStatus) {
                case ServerStatus.NotStarted:
                    this.view.text = "$(debug-start) Caesar Inactive";
                    this.view.command = "caesar.startServer";
                    break;
                case ServerStatus.Stopped:
                    this.view.text = "$(debug-start) Et tu, Brute?";
                    this.view.command = "caesar.startServer";
                    break;
                case ServerStatus.FailedToStart:
                    this.view.text = "$(warning) Failed to start Caesar";
                    this.view.command = "caesar.startServer";
                    break;
                case ServerStatus.Starting:
                    this.view.text = "$(sync~spin) Starting Caesar...";
                    this.view.command = ""
                    break;
                case ServerStatus.Ready:
                    this.view.text = "$(thumbsup-filled) Caesar Ready";
                    this.view.command = "caesar.showOutput";
                    break;
                case ServerStatus.Verifying:
                    this.view.text = "$(sync~spin) Verifying...";
                    this.view.command = ""
                    break;
                case ServerStatus.Finished:
                    this.handleFinishedStatus()
                    // If no errors are present, show the verified status
                    // this.view.text = "$(check) Verified";
                    this.view.command = "caesar.showOutput";
                    break;
            }
            this.view.show();
        } else {
            this.view.hide();
        }
    }

    private handleFinishedStatus() {
        let returnString = "";
        let everythingVerified = true;
        let openEditorCount = 0;

        let verified = 0;
        let failed = 0;
        let unknown = 0;
        for (const [document_id, results] of this.verifyStatus.entries()) {
            for (const editor of vscode.window.visibleTextEditors) {

                if (editor.document.languageId !== "heyvl") {
                    continue;
                }
                openEditorCount++;

                if (editor.document.uri.toString() !== document_id.uri) {
                    continue;
                }

                verified = 0;
                failed = 0;
                unknown = 0;

                for (const [_, result] of results) {
                    switch (result) {
                        case VerifyResult.Verified:
                            verified++;
                            break;
                        case VerifyResult.Failed:
                            failed++;
                            break;
                        case VerifyResult.Unknown:
                            unknown++;
                            break;
                    }
                }

                if (failed > 0 || unknown > 0) {
                    everythingVerified = false;
                }

                returnString += `${vscode.Uri.parse(document_id.uri).path}: \n $(error) ${failed} $(question) ${unknown}\n---\n`;
            }
        }

        if (everythingVerified) {
            this.view.text = "$(pass) Verified!";
            this.view.tooltip = new vscode.MarkdownString("No errors found", true);
        } else {
            this.view.text = `$(warning) Verification Errors $(error) ${failed} $(question) ${unknown}`;
            this.view.tooltip = new vscode.MarkdownString(returnString.trim(), true);
        }

    }


}
