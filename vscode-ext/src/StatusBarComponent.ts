import { StatusBarItem, Range } from "vscode";
import * as vscode from 'vscode';
import { StatusBarViewConfig } from "./Config";
import { ServerStatus, VerifyResult } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";
import { ConfigurationConstants } from "./constants";
import { TextDocumentIdentifier } from "vscode-languageclient";


const runningTooltipMenu =
    new vscode.MarkdownString(
        "[Stop Caesar](command:caesar.stopServer)\n\n" +
        "[Restart Caesar](command:caesar.restartServer)"
        , true);

const stoppedTooltipMenu =
    new vscode.MarkdownString(
        "[Start Caesar](command:caesar.startServer)", true);

export class StatusBarComponent {

    private enabled: boolean;
    private verifyStatus: DocumentMap<[Range, VerifyResult][]> = new DocumentMap();
    private serverStatus: ServerStatus = ServerStatus.NotStarted;
    private view: StatusBarItem;
    private tooltipMenuText: vscode.MarkdownString = stoppedTooltipMenu;
    private tooltipStatusText: vscode.MarkdownString = new vscode.MarkdownString();

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

        verifier.context.subscriptions.push(vscode.workspace.onDidCloseTextDocument((document) => {
            const documentIdentifier: TextDocumentIdentifier = { uri: document.uri.toString() };
            this.verifyStatus.remove(documentIdentifier);
            this.render();
        }));

        verifier.context.subscriptions.push(vscode.window.onDidChangeVisibleTextEditors(() => {
            this.render();
        }));

        verifier.context.subscriptions.push(vscode.workspace.onDidOpenTextDocument(() => {
            this.render();
        }));
    }

    render() {
        if (this.enabled) {

            switch (this.serverStatus) {
                case ServerStatus.NotStarted:
                    this.view.text = "$(debug-start) Caesar Inactive";
                    this.view.command = "caesar.startServer";
                    this.tooltipMenuText = stoppedTooltipMenu;
                    break;
                case ServerStatus.Stopped:
                    this.view.text = "$(debug-start) Et tu, Brute?";
                    this.view.command = "caesar.startServer";
                    this.tooltipMenuText = stoppedTooltipMenu;
                    break;
                case ServerStatus.FailedToStart:
                    this.view.text = "$(warning) Failed to start Caesar";
                    this.view.command = "caesar.startServer";
                    this.tooltipMenuText = stoppedTooltipMenu;
                    break;
                case ServerStatus.Starting:
                    this.view.text = "$(loading~spin) Starting Caesar...";
                    this.view.command = "caesar.showOutput"
                    break;
                case ServerStatus.Ready:
                    this.handleReadyStatus();
                    this.view.command = "caesar.showOutput";
                    this.tooltipMenuText = runningTooltipMenu;
                    break;
                case ServerStatus.Verifying:
                    this.view.text = "$(sync~spin) Verifying...";
                    this.view.command = "caesar.showOutput"
                    break;
            }

            this.renderTooltip();
            this.view.show();
        } else {
            this.view.hide();
        }
    }

    private renderTooltip() {
        if (this.tooltipStatusText.value === "") {
            this.view.tooltip = this.tooltipMenuText;
            this.view.tooltip.isTrusted = true;
            return;
        }
        this.view.tooltip = new vscode.MarkdownString(this.tooltipMenuText.value + "\n\n --- \n" + this.tooltipStatusText.value, true);
        this.view.tooltip.isTrusted = true;
    }


    private handleReadyStatus() {
        let tooltipString = new vscode.MarkdownString("", true);

        let someError = false;
        let someVerified = false;

        const editorsWithResults = vscode.window.visibleTextEditors.filter((editor) => {
            return editor.document.languageId === "heyvl" // Only HeyVL files
                && (this.verifyStatus.get({ uri: editor.document.uri.toString() }) ?? []).length !== 0; // And only files with results
        });

        if (editorsWithResults.length === 0) {
            // No HeyVL files open or no results yet
            this.view.text = "$(thumbsup-filled) Caesar Ready";
            return;
        }

        for (const editor of editorsWithResults) {
            const document_id: TextDocumentIdentifier = { uri: editor.document.uri.toString() };

            // The default will not be used because the filter above ensures that the document is in the map.
            const results = this.verifyStatus.get(document_id) ?? [];

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

            if (failed > 0 || unknown > 0) {
                someError = true;
            }
            if (verified > 0) {
                someVerified = true;
            }

            tooltipString.appendMarkdown(`${vscode.Uri.parse(document_id.uri).path}: $(error) ${failed} $(question) ${unknown}` + "\n\n --- \n");
        }


        // Remove the last newline and separator
        tooltipString.value.trimEnd();


        if (!someError && someVerified) {
            // No error and at least one verified implies everything is verified.
            this.view.text = "$(pass) Verified!";
            this.tooltipStatusText = new vscode.MarkdownString("No errors found", true);

        } else if (someError) {
            // At least one verified, but some errors
            this.view.text = "$(warning) Verification Errors";
            this.tooltipStatusText = tooltipString;
        }
        else if (!someError && !someVerified) {
            // No error and no verified implies the file is either empty or there are syntax errors.
            this.view.text = "$(error) Invalid File";
            this.tooltipStatusText = new vscode.MarkdownString("Syntax error or empty file!", true);
        }
    }

}



