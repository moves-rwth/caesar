import { StatusBarItem, Range } from "vscode";
import * as vscode from 'vscode';
import { StatusBarViewConfig } from "./Config";
import { ServerStatus, VerifyResult } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";
import { ConfigurationConstants } from "./constants";


const runningTooltipBase =
    new vscode.MarkdownString(
        "[Stop Caesar](command:caesar.stopServer)\n\n" +
        "[Restart Caesar](command:caesar.restartServer)"
        , true);

const stoppedTooltipBase =
    new vscode.MarkdownString(
        "[Start Caesar](command:caesar.startServer)", true);

export class StatusBarComponent {

    private enabled: boolean;
    private verifyStatus: DocumentMap<[Range, VerifyResult][]> = new DocumentMap();
    private serverStatus: ServerStatus = ServerStatus.NotStarted;
    private view: StatusBarItem;
    private tooltipBase: vscode.MarkdownString = stoppedTooltipBase;
    private tooltipExtension: vscode.MarkdownString = new vscode.MarkdownString();

    constructor(verifier: Verifier) {
        // create the view
        this.view = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 99);
        verifier.context.subscriptions.push(this.view);
        this.view.text = "Caesar";
        this.view.command = "caesar.showOutput";


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
                    this.tooltipBase = stoppedTooltipBase;
                    break;
                case ServerStatus.Stopped:
                    this.view.text = "$(debug-start) Et tu, Brute?";
                    this.view.command = "caesar.startServer";
                    this.tooltipBase = stoppedTooltipBase;
                    break;
                case ServerStatus.FailedToStart:
                    this.view.text = "$(warning) Failed to start Caesar";
                    this.view.command = "caesar.startServer";
                    this.tooltipBase = stoppedTooltipBase;
                    break;
                case ServerStatus.Starting:
                    this.view.text = "$(loading~spin) Starting Caesar...";
                    this.view.command = ""
                    break;
                case ServerStatus.Ready:
                    this.view.text = "$(thumbsup-filled) Caesar Ready";
                    this.view.command = "caesar.showOutput";
                    this.tooltipBase = runningTooltipBase;
                    break;
                case ServerStatus.Verifying:
                    this.view.text = "$(sync~spin) Verifying...";
                    this.view.command = ""
                    break;
                case ServerStatus.Finished:
                    this.tooltipBase = runningTooltipBase;
                    this.handleFinishedStatus();
                    this.view.command = "caesar.showOutput";
                    break;
            }

            this.renderTooltip();
            this.view.show();
        } else {
            this.view.hide();
        }
    }

    private extendedTooltip(extension: vscode.MarkdownString) {
        return new vscode.MarkdownString(this.tooltipBase.value + "\n\n --- \n" + extension.value, true);
    }

    private renderTooltip() {
        if (this.tooltipExtension.value === "") {
            this.view.tooltip = this.tooltipBase;
            this.view.tooltip.isTrusted = true;
            return;
        }
        this.view.tooltip = this.extendedTooltip(this.tooltipExtension);
        this.view.tooltip.isTrusted = true;
    }

    private countResults(results: [Range, VerifyResult][]): [number, number, number] {
        let verified = 0;
        let failed = 0;
        let unknown = 0;

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

        return [verified, failed, unknown];
    }


    private handleFinishedStatus() {
        let tooltipString = new vscode.MarkdownString("", true);

        let everythingVerified = true;

        for (const [document_id, results] of this.verifyStatus.entries()) {
            for (const editor of vscode.window.visibleTextEditors) {

                if (editor.document.languageId !== "heyvl") {
                    continue;
                }

                if (editor.document.uri.toString() !== document_id.uri) {
                    continue;
                }

                let [verified, failed, unknown] = this.countResults(results);

                if (failed > 0 || unknown > 0) {
                    everythingVerified = false;
                }

                tooltipString.appendMarkdown(`${vscode.Uri.parse(document_id.uri).path}: $(error) ${failed} $(question) ${unknown}` + "\n\n --- \n");
            }
        }

        // Remove the last newline and separator
        tooltipString.value.trimEnd();

        if (everythingVerified) {
            this.view.text = "$(pass) Verified!";
            this.tooltipExtension = new vscode.MarkdownString("No errors found", true);
        } else {
            this.view.text = "$(warning) Verification Errors";
            this.tooltipExtension = tooltipString;
        }

    }


}
