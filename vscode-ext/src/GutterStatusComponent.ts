import { Range } from "vscode";
import * as vscode from 'vscode';
import { GutterInformationViewConfig } from "./Config";
import { ServerStatus, VerifyResult } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";
import { ConfigurationConstants } from "./constants";
import { TextDocumentIdentifier } from "vscode-languageclient";

export class GutterStatusComponent {

    private enabled: boolean;
    private status: DocumentMap<[Range, VerifyResult][]>;
    private serverStatus: ServerStatus = ServerStatus.NotStarted;
    private gutterAnimator: GutterAnimator;

    private verifyDecType: vscode.TextEditorDecorationType;
    private failedDecType: vscode.TextEditorDecorationType;
    private unknownDecType: vscode.TextEditorDecorationType;
    private timeoutDecType: vscode.TextEditorDecorationType;

    constructor(verifier: Verifier) {

        // Load the fixed decoration types
        this.verifyDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath('images/verified.png') });
        this.failedDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath('images/failed.png') });
        this.unknownDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath('images/unknown.png') });
        this.timeoutDecType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath('images/timeout.png') });

        // Load the animation frames
        let frameDecorationMap: Map<number, vscode.TextEditorDecorationType> = new Map();
        for (let i = 0; i < 8; i++) {
            let decType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath(`images/gutterAnimation/${i}.png`) });
            frameDecorationMap.set(i, decType);
        }

        // render if enabled
        this.enabled = GutterInformationViewConfig.get(ConfigurationConstants.showGutterIcons);

        this.status = new DocumentMap();

        this.gutterAnimator = new GutterAnimator(frameDecorationMap);

        // Editor context subscriptions:
        // ----------------------------

        // subscribe to config changes
        verifier.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (GutterInformationViewConfig.isAffected(e)) {
                this.enabled = GutterInformationViewConfig.get(ConfigurationConstants.showGutterIcons);
                this.render();
            }
        }));

        // render when visible editors change
        verifier.context.subscriptions.push(vscode.window.onDidChangeVisibleTextEditors(() => {
            this.render();
        }));


        verifier.context.subscriptions.push(vscode.workspace.onDidCloseTextDocument((document) => {
            const documentIdentifier: TextDocumentIdentifier = { uri: document.uri.toString() };
            this.status.remove(documentIdentifier);
            this.render();
        }));

        // Server context subscriptions:
        // ----------------------------

        // listen to status and verify updates
        verifier.client.onStatusUpdate((status) => {
            this.serverStatus = status;
            if (status === ServerStatus.Verifying) {
                for (const [_document, results] of this.status.entries()) {
                    results.length = 0;
                }
            }
            this.render();
        });

        verifier.client.onVerifyResult((document, results) => {
            this.status.insert(document, results);
            this.render();
        });

    }

    render() {
        let loadingEditorRangeMap: Map<vscode.TextEditor, vscode.Range[]> = new Map();

        for (const editor of vscode.window.visibleTextEditors) {
            for (const [document_id, results] of this.status.entries()) {

                if (editor.document.uri.toString() !== document_id.uri) {
                    continue;
                }

                const verifiedProcs: vscode.DecorationOptions[] = [];
                const failedProcs: vscode.DecorationOptions[] = [];
                const unknownProcs: vscode.DecorationOptions[] = [];
                const timeoutProcs: vscode.DecorationOptions[] = [];

                const todoProcs: Range[] = [];

                if (this.enabled) {
                    for (const [range, result] of results) {
                        const line = range.start.line;
                        const gutterRange = new vscode.Range(line, 0, line, 0);

                        switch (result) {
                            case VerifyResult.Todo:
                                if (this.serverStatus === ServerStatus.Ready) {
                                    // If the server stopped verfying, but this is still todo, mark as unknown
                                    // This should not happen since the server converts todos to timeouts when it stops verifying
                                    unknownProcs.push({ range: gutterRange, hoverMessage: 'Unknown' });
                                }

                                // Add to the todo list to be animated
                                todoProcs.push(range);
                                break;
                            case VerifyResult.Verified:
                                verifiedProcs.push({ range: gutterRange, hoverMessage: 'Verified' });
                                break;
                            case VerifyResult.Failed:
                                failedProcs.push({ range: gutterRange, hoverMessage: 'Not Verified' });
                                break;
                            case VerifyResult.Unknown:
                                unknownProcs.push({ range: gutterRange, hoverMessage: 'Unknown' });
                                break;
                            case VerifyResult.Timeout:
                                timeoutProcs.push({ range: gutterRange, hoverMessage: 'Timeout' });
                        }
                    }
                }
                loadingEditorRangeMap.set(editor, todoProcs);

                editor.setDecorations(this.verifyDecType, verifiedProcs);
                editor.setDecorations(this.failedDecType, failedProcs);
                editor.setDecorations(this.unknownDecType, unknownProcs);
                editor.setDecorations(this.timeoutDecType, timeoutProcs);
            }
        }
        this.gutterAnimator.setEditorRangemap(loadingEditorRangeMap);

    }
}

class GutterAnimator {
    private frame = 0;
    private interval: NodeJS.Timeout | undefined;

    private editorRangeMap: Map<vscode.TextEditor, vscode.Range[]> = new Map();

    constructor(private readonly frameDecorationMap: Map<number, vscode.TextEditorDecorationType>, private readonly intervalSpeed: number = 75) {
    }

    startAnimation() {
        if (this.interval === undefined) {
            this.interval = setInterval(() => {
                this.frame = (this.frame + 1) % this.frameDecorationMap.size;
                this.render();
            }, this.intervalSpeed);
        }
    }

    stopAnimation() {
        if (this.interval !== undefined) {
            clearInterval(this.interval);
            this.interval = undefined;
        }
    }

    setEditorRangemap(editorRangeMap: Map<vscode.TextEditor, vscode.Range[]>) {
        this.editorRangeMap = editorRangeMap;
        if (Array.from(editorRangeMap.values()).every(ranges => ranges.length == 0)) {
            // Animation is not needed if there are no ranges to animate
            this.stopAnimation();
            // Render to clear the decorations
            this.render();
        } else {
            // If the animation is still running, it won't be restarted internally 
            // so it is safe to call startAnimation multiple times
            this.startAnimation();
        }

    }

    render() {
        // const decorations = this.frameDecorationMap.get(this.frame) ?? [];
        // for each decoration type in the map
        for (const [frame, decType] of this.frameDecorationMap) {
            for (const [editor, ranges] of this.editorRangeMap) {
                // if the frame is the current frame
                if (frame === this.frame) {
                    // set the decorations
                    editor.setDecorations(decType, ranges.map(range => ({ range: range, hoverMessage: 'Pending' })));
                } else {
                    // clear the decorations for other frames
                    editor.setDecorations(decType, []);
                }
            }

        }
    }
}
