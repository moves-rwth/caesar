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
        let viewText = "";
        let command = "";
        let tooltipMenuText = new vscode.MarkdownString();
        let tooltipStatusText = new vscode.MarkdownString();
        if (this.enabled) {

            switch (this.serverStatus) {
                case ServerStatus.NotStarted:
                    viewText = "$(debug-start) Caesar Inactive";
                    command = "caesar.startServer";
                    tooltipMenuText = stoppedTooltipMenu;
                    break;
                case ServerStatus.Stopped:
                    viewText = "$(debug-start) Et tu, Brute?";
                    command = "caesar.startServer";
                    tooltipMenuText = stoppedTooltipMenu;
                    break;
                case ServerStatus.FailedToStart:
                    viewText = "$(warning) Failed to start Caesar";
                    command = "caesar.startServer";
                    tooltipMenuText = stoppedTooltipMenu;
                    break;
                case ServerStatus.Starting:
                    viewText = "$(loading~spin) Starting Caesar...";
                    command = "caesar.showOutput"
                    break;
                case ServerStatus.Ready:
                    [viewText, tooltipStatusText] = this.getReadyStatusView();
                    command = "caesar.showOutput";
                    tooltipMenuText = runningTooltipMenu;
                    break;
                case ServerStatus.Verifying:
                    viewText = "$(sync~spin) Verifying...";
                    command = "caesar.showOutput"
                    break;
            }

            this.view.text = viewText;
            this.view.command = command;
            this.renderTooltip(tooltipMenuText, tooltipStatusText);
            this.view.show();
        } else {
            this.view.hide();
        }
    }

    /// Renders the tooltip by combining the given menu and status text.
    private renderTooltip(tooltipMenuText: vscode.MarkdownString, tooltipStatusText: vscode.MarkdownString) {
        if (tooltipStatusText.value === "") {
            this.view.tooltip = tooltipMenuText;
            this.view.tooltip.isTrusted = true;
            return;
        }
        this.view.tooltip = new vscode.MarkdownString(tooltipMenuText.value + "\n\n --- \n" + tooltipStatusText.value, true);
        this.view.tooltip.isTrusted = true;
    }


    /// Returns the status view text and tooltip for the ready status by aggregating the verification results for each visible editor.
    private getReadyStatusView(): [string, vscode.MarkdownString] {
        let viewText = "";
        let tooltipString = new vscode.MarkdownString("", true);

        let someError = false;
        let someVerified = false;

        const editorsWithResults = vscode.window.visibleTextEditors.filter((editor) => {
            return (this.verifyStatus.get({ uri: editor.document.uri.toString() }) ?? []).length !== 0; // And only files with results
        });

        if (editorsWithResults.length === 0) {
            return ["$(thumbsup-filled) Caesar Ready", new vscode.MarkdownString("Verify some HeyVL files!", true)];
        }

        for (const editor of editorsWithResults) {
            const document_id: TextDocumentIdentifier = { uri: editor.document.uri.toString() };

            const results = this.verifyStatus.get(document_id);

            if (results === undefined) throw new Error("No verify results found for document: " + document_id);

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
            viewText = "$(pass) Verified!";
            tooltipString = new vscode.MarkdownString("No errors found", true);
        } else if (someError) {
            // At least one verified, but some errors
            viewText = "$(warning) Verification Errors";
        } else if (!someError && !someVerified) {
            // No error and no verified implies the file is either empty or there are syntax errors.
            viewText = "$(error) Invalid File";
            tooltipString = new vscode.MarkdownString("Syntax error or empty file!", true);
        }

        return [viewText, tooltipString];

    }

}



