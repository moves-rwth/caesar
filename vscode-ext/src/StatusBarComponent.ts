import { StatusBarItem } from "vscode";
import * as vscode from 'vscode';
import { StatusBarViewConfig } from "./Config";
import { DocumentStatus, DocumentStatusType, ServerStatus, VerifyResult } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";
import { ConfigurationConstants } from "./constants";
import { TextDocumentIdentifier } from "vscode-languageclient";


enum TooltipMenuType {
    running = "running",
    stopped = "stopped",
}

enum Command {
    StartServer = "caesar.startServer",
    StopServer = "caesar.stopServer",
    RestartServer = "caesar.restartServer",
    ShowOutput = "caesar.showOutput",
}


interface StatusBarModel { tooltip_menu_type: TooltipMenuType, tooltip_status_text: vscode.MarkdownString, bar_text: string, command: Command }

export class StatusBarComponent {

    private enabled: boolean;
    private documentStatuses = new DocumentMap<DocumentStatus>();

    private latestActiveHeyvlEditor: vscode.TextEditor | undefined = vscode.window.activeTextEditor?.document.languageId === "heyvl" ? vscode.window.activeTextEditor : undefined;

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

        verifier.client.onDocumentVerifyStatus((update) => {
            this.documentStatuses.insert(update.document, update);
            this.render();
        });

        verifier.context.subscriptions.push(vscode.workspace.onDidCloseTextDocument((document) => {
            const documentIdentifier: TextDocumentIdentifier = { uri: document.uri.toString() };
            this.documentStatuses.remove(documentIdentifier);
            this.render();
        }));

        verifier.context.subscriptions.push(vscode.window.onDidChangeVisibleTextEditors(() => {
            if (vscode.window.visibleTextEditors.length === 0 || vscode.window.visibleTextEditors.every(editor => editor.document.languageId !== "heyvl")) {
                this.latestActiveHeyvlEditor = undefined;
            }
            this.render();
        }));

        verifier.context.subscriptions.push(vscode.workspace.onDidOpenTextDocument(() => {
            this.render();
        }));

        verifier.context.subscriptions.push(vscode.window.onDidChangeActiveTextEditor(() => {
            // If the new active editor is a heyvl file
            if (vscode.window.activeTextEditor?.document.languageId === "heyvl") {
                this.latestActiveHeyvlEditor = vscode.window.activeTextEditor;
            }
            this.render();
        }));
    }

    render() {
        const document_status = this.documentStatuses.get({ uri: this.latestActiveHeyvlEditor?.document.uri.toString() ?? "" });
        const model = this.mapStatusToModel(this.serverStatus, document_status);

        if (this.enabled) {
            this.view.text = model.bar_text;
            this.view.command = model.command;
            this.renderAndSetTooltip(model);
            this.view.show();
        } else {
            this.view.hide();
        }
    }

    /// Render the tooltip by combining the given menu and status text and then sets it to the view.
    private renderAndSetTooltip(model: StatusBarModel) {

        const tooltipMenuType = model.tooltip_menu_type;
        const tooltipStatusText = model.tooltip_status_text;

        const renderedMenu = this.renderTooltipMenu(tooltipMenuType);
        const list = this.renderTooltipResultsList();

        if (list.value.length === 0 && tooltipStatusText.value === "") {
            this.view.tooltip = renderedMenu;
            this.view.tooltip.isTrusted = true;
            return;
        }
        this.view.tooltip = new vscode.MarkdownString(renderedMenu.value + "\n\n --- \n" + list.appendMarkdown(tooltipStatusText.value).value, true);
        this.view.tooltip.isTrusted = true;
    }

    /// Render the results list (per verified heyvl file) based on the current document statuses.
    private renderTooltipResultsList(): vscode.MarkdownString {
        const tooltipString = new vscode.MarkdownString("", true);
        const editorsWithResults = vscode.window.visibleTextEditors.filter((editor) => {
            return ((this.documentStatuses.get({ uri: editor.document.uri.toString() }))?.verify_statuses ?? []).length !== 0; // And only files with results
        });


        for (const editor of editorsWithResults) {
            const document_id: TextDocumentIdentifier = { uri: editor.document.uri.toString() };

            const document_status = this.documentStatuses.get(document_id);

            const status_counts = new Map<VerifyResult, number>(document_status?.status_counts ?? []);
            // const _verified = status_counts.get(VerifyResult.Verified) ?? 0;
            const failed = status_counts.get(VerifyResult.Failed) ?? 0;
            const unknown = status_counts.get(VerifyResult.Unknown) ?? 0 + (status_counts.get(VerifyResult.Timeout) ?? 0);

            tooltipString.appendMarkdown(`${vscode.workspace.asRelativePath(vscode.Uri.parse(document_id.uri).path)}: $(error) ${failed} $(question) ${unknown}` + "\n\n --- \n");
        }
        // Remove the last newline and separator
        tooltipString.value.trimEnd();

        return tooltipString;
    }

    /// Render the tooltip menu based on the given menu type.
    private renderTooltipMenu(menu: TooltipMenuType): vscode.MarkdownString {
        switch (menu) {
            case TooltipMenuType.running:
                return new vscode.MarkdownString(
                    "[Stop Caesar](command:caesar.stopServer)\n\n" +
                    "[Restart Caesar](command:caesar.restartServer)"
                    , true);
            case TooltipMenuType.stopped:
                return new vscode.MarkdownString(
                    "[Start Caesar](command:caesar.startServer)", true);
        }
    }

    /// Map the server status and document status to a model for the status bar that can be rendered.
    private mapStatusToModel(server_status: ServerStatus, document_status: DocumentStatus | undefined): StatusBarModel {
        let model = {
            tooltip_menu_type: TooltipMenuType.stopped,
            tooltip_status_text: new vscode.MarkdownString("Caesar server is not running.", true),
            bar_text: "$(debug-start) Caesar Not Started",
            command: Command.StartServer
        } as StatusBarModel;

        switch (server_status) {
            case ServerStatus.NotStarted:
                model = {
                    tooltip_menu_type: TooltipMenuType.stopped,
                    tooltip_status_text: new vscode.MarkdownString("Caesar server is not running.", true),
                    bar_text: "$(debug-start) Caesar Not Started",
                    command: Command.StartServer
                };
                break;
            case ServerStatus.Stopped:
                model = {
                    tooltip_menu_type: TooltipMenuType.stopped,
                    tooltip_status_text: new vscode.MarkdownString("Caesar server is stopped.", true),
                    bar_text: "$(debug-start) Et tu, Brute?",
                    command: Command.StartServer
                };
                break;
            case ServerStatus.FailedToStart:
                model = {
                    tooltip_status_text: new vscode.MarkdownString("Caesar server failed to start. Check the output for more details.", true),
                    tooltip_menu_type: TooltipMenuType.stopped,
                    bar_text: "$(debug-start) Caesar Failed To Start",
                    command: Command.StartServer
                };
                break;
            case ServerStatus.Starting:
                model = {
                    tooltip_status_text: new vscode.MarkdownString("Caesar server is starting...", true),
                    tooltip_menu_type: TooltipMenuType.running,
                    bar_text: "$(loading~spin) Starting Caesar...",
                    command: Command.ShowOutput
                };
                break;
            case ServerStatus.Ready:
                switch (document_status?.status_type) {
                    case DocumentStatusType.Invalid:
                        model = {
                            bar_text: "$(error) Invalid File",
                            tooltip_menu_type: TooltipMenuType.running,
                            tooltip_status_text: new vscode.MarkdownString("File can not be verified.", true),
                            command: Command.ShowOutput
                        };
                        break;
                    case DocumentStatusType.Timeout:
                        model = {
                            bar_text: "$(error) Timeout",
                            tooltip_menu_type: TooltipMenuType.running,
                            tooltip_status_text: new vscode.MarkdownString("File verification timed out.", true),
                            command: Command.ShowOutput
                        };
                        break;
                    case DocumentStatusType.Todo:
                    case DocumentStatusType.Done: {
                        const someError = document_status?.status_counts.some(([result, _count]) => result === VerifyResult.Failed || result === VerifyResult.Timeout || result === VerifyResult.Unknown) ?? false;
                        const someVerified = document_status?.status_counts.some(([result, _count]) => result === VerifyResult.Verified) ?? false;

                        if (!someError && someVerified) {
                            // No error and at least one verified implies everything is verified.
                            model = {
                                tooltip_menu_type: TooltipMenuType.running,
                                tooltip_status_text: new vscode.MarkdownString("All procedures verified successfully.", true),
                                bar_text: "$(pass) Verified!",
                                command: Command.ShowOutput
                            };
                        } else if (someError) {
                            // At least one verified, but some errors
                            model = {
                                bar_text: "$(warning) Verification Errors",
                                tooltip_menu_type: TooltipMenuType.running,
                                tooltip_status_text: new vscode.MarkdownString("Some procedures failed verification. Check the output for details.", true),
                                command: Command.ShowOutput
                            };
                        } else if (!someError && !someVerified) {
                            // No error and no verified implies the file does not contain procedures yet.
                            model = this.cleanReadyModel();
                        }
                        break;
                    }
                    case undefined:
                        // No document status means the file is not verified yet or there are no valid file open.
                        model = this.cleanReadyModel();
                        break;
                }
                break;
            case ServerStatus.Verifying:
                model.tooltip_menu_type = TooltipMenuType.running;
                model.bar_text = "$(sync~spin) Verifying...";
                model.command = Command.ShowOutput;
                break;
            case ServerStatus.Error:
                model.tooltip_menu_type = TooltipMenuType.running;
                model.bar_text = "$(warning) Error";
                model.command = Command.ShowOutput;
                break;
        }
        return model;
    }

    /// Return the clean ready model for the status bar when there are no procedures verified yet.
    private cleanReadyModel(): StatusBarModel {
        return {
            tooltip_menu_type: TooltipMenuType.running,
            tooltip_status_text: new vscode.MarkdownString("Verify some HeyVL files!", true),
            bar_text: "$(thumbsup-filled) Caesar Ready",
            command: Command.ShowOutput
        };
    }
}





