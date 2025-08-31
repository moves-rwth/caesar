import { Range } from "vscode";
import * as vscode from 'vscode';
import { GutterInformationViewConfig } from "./Config";
import { DocumentStatus, ServerStatus, VerifyResult } from "./CaesarClient";
import { DocumentMap, Verifier } from "./Verifier";
import { ConfigurationConstants } from "./constants";
import { TextDocumentIdentifier } from "vscode-languageclient";


const FRAME_COUNT = 2; // Number of frames in the animation
const FRAME_INTERVAL = 300; // Interval between frames in milliseconds
const ANIMATION_PATH = "images/gutterAnimation/"; // Path to the animation frames
const THEME_SENSITIVE = false;
const ANIMATION_NAME = "laurel"; // Name of the animation
const ANIMATION_EXT = "svg"; // Extension of the animation frames

export class GutterStatusComponent {

    private enabled: boolean;
    private animEnabled: boolean;
    private status: DocumentMap<DocumentStatus>;
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

        // render if enabled
        this.enabled = GutterInformationViewConfig.get(ConfigurationConstants.showGutterIcons);

        this.animEnabled = GutterInformationViewConfig.get(ConfigurationConstants.showGutterAnimation);

        this.status = new DocumentMap();

        this.gutterAnimator = new GutterAnimator();
        this.gutterAnimator.setEnabled(this.animEnabled);


        if (THEME_SENSITIVE) {
            // Load the animation frames
            for (const theme of ["light", "dark"]) {
                const frameDecs = createFrameDecorations(`${ANIMATION_PATH}/${ANIMATION_NAME}-${theme}-`, ANIMATION_EXT, FRAME_COUNT, verifier);

                this.gutterAnimator.loadAnimationFrames(`${ANIMATION_NAME}-${theme}`, frameDecs);

                // Set the initial animation
                this.gutterAnimator.changeAnimation(`${ANIMATION_NAME}-${themeToAnimationName(vscode.window.activeColorTheme)}`);
            }
        }
        else {
            const frameDecs = createFrameDecorations(`${ANIMATION_PATH}/${ANIMATION_NAME}-`, ANIMATION_EXT, FRAME_COUNT, verifier);
            this.gutterAnimator.loadAnimationFrames(ANIMATION_NAME, frameDecs);

            // Set the initial animation
            this.gutterAnimator.changeAnimation(ANIMATION_NAME);
        }


        // Editor context subscriptions:
        // ----------------------------

        // subscribe to config changes
        verifier.context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (GutterInformationViewConfig.isAffected(e)) {
                this.enabled = GutterInformationViewConfig.get(ConfigurationConstants.showGutterIcons);
                this.animEnabled = GutterInformationViewConfig.get(ConfigurationConstants.showGutterAnimation);
                this.gutterAnimator.setEnabled(this.animEnabled);
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

        verifier.context.subscriptions.push(vscode.window.onDidChangeActiveColorTheme((newTheme) => {
            if (THEME_SENSITIVE) {
                this.gutterAnimator.changeAnimation(`${ANIMATION_NAME}-${themeToAnimationName(newTheme)}`);
            }
        }));


        // Server context subscriptions:
        // ----------------------------

        // listen to status and verify updates
        verifier.client.onStatusUpdate((status) => {
            this.serverStatus = status;
            if (status === ServerStatus.Verifying) {
                for (const [_document, status] of this.status.entries()) {
                    status.verify_statuses.length = 0;
                }
            }
            this.render();
        });

        verifier.client.onDocumentVerifyStatus((update) => {
            this.status.insert(update.document, update);
            this.render();
        });

    }

    render() {
        let loadingEditorRangeMap: Map<vscode.TextEditor, vscode.Range[]> = new Map();

        for (const editor of vscode.window.visibleTextEditors) {
            for (const [document_id, status] of this.status.entries()) {

                let results = status.verify_statuses;

                if (editor.document.uri.toString() !== document_id.uri) {
                    continue;
                }

                const verifiedProcs: vscode.DecorationOptions[] = [];
                const failedProcs: vscode.DecorationOptions[] = [];
                const unknownProcs: vscode.DecorationOptions[] = [];

                const todoProcs: Range[] = [];

                if (this.enabled) {
                    for (const [range, result] of results) {
                        const line = range.start.line;
                        const gutterRange = new vscode.Range(line, 0, line, 0);

                        switch (result) {
                            case VerifyResult.Todo:
                            case VerifyResult.Ongoing:
                                if (this.serverStatus === ServerStatus.Ready) {
                                    // If the server stopped verfying, but this is still todo, mark as unknown
                                    // This should not happen since the server converts todos to timeouts when it stops verifying
                                    unknownProcs.push({ range: gutterRange });
                                }

                                // Add to the todo list to be animated
                                todoProcs.push(range);
                                break;
                            case VerifyResult.Verified:
                                verifiedProcs.push({ range: gutterRange });
                                break;
                            case VerifyResult.Failed:
                                failedProcs.push({ range: gutterRange });
                                break;
                            case VerifyResult.Unknown:
                                unknownProcs.push({ range: gutterRange });
                                break;
                            case VerifyResult.Timeout:
                                unknownProcs.push({ range: gutterRange });
                        }
                    }
                }
                loadingEditorRangeMap.set(editor, todoProcs);

                editor.setDecorations(this.verifyDecType, verifiedProcs);
                editor.setDecorations(this.failedDecType, failedProcs);
                editor.setDecorations(this.unknownDecType, unknownProcs);

            }
        }
        this.gutterAnimator.setEditorRangemap(loadingEditorRangeMap);
    }
}

class GutterAnimator {
    private enabled: boolean = false;
    private frame = 0;
    private interval: NodeJS.Timeout | undefined;
    private intervalSpeed: number;

    private editorRangeMap: Map<vscode.TextEditor, vscode.Range[]> = new Map();
    private animationTypes: Map<string, vscode.TextEditorDecorationType[]> = new Map();
    private currentAnimationName: string = "";


    constructor(intervalSpeed: number = FRAME_INTERVAL) {
        this.intervalSpeed = intervalSpeed;
    }

    loadAnimationFrames(name: string, frameDecorations: vscode.TextEditorDecorationType[]) {
        this.animationTypes.set(name, frameDecorations);
    }

    getCurrentAnimationFrames(): vscode.TextEditorDecorationType[] {
        return this.animationTypes.get(this.currentAnimationName) || [];
    }

    startAnimation() {
        if (this.interval === undefined) {
            this.frame = 0;
            this.interval = setInterval(() => {
                this.frame = (this.frame + 1) % this.getCurrentAnimationFrames().length;
                this.render();
            }, this.intervalSpeed);
        }
    }

    stopAnimation() {
        if (this.interval !== undefined) {
            clearInterval(this.interval);
            this.interval = undefined;
            this.clearAnimation();
        }
    }

    changeAnimation(name: string) {
        this.stopAnimation();
        this.currentAnimationName = name;
        this.startAnimation();
    }

    clearAnimation() {
        for (const [_frame, decType] of this.getCurrentAnimationFrames().entries()) {
            for (const [editor, _ranges] of this.editorRangeMap) {
                editor.setDecorations(decType, []);
            }
        }
    }

    setEnabled(enabled: boolean) {
        this.enabled = enabled;
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
        if (!this.enabled) {
            return;
        }
        // for each decoration type in the map
        for (const [frame, decType] of this.getCurrentAnimationFrames().entries()) {
            for (const [editor, ranges] of this.editorRangeMap) {
                // if the frame is the current frame, set the decoration
                // else clear the decoration
                editor.setDecorations(decType, frame === this.frame ? ranges : []);
            }
        }
    }
}

function createFrameDecorations(path: string, file_ext: string, frameCount: number, verifier: Verifier): vscode.TextEditorDecorationType[] {
    // Create the decoration types for the animation frames
    let frameDecorationList: vscode.TextEditorDecorationType[] = [];
    for (let i = 0; i < frameCount; i++) {
        let decType = vscode.window.createTextEditorDecorationType({ gutterIconSize: "contain", gutterIconPath: verifier.context.asAbsolutePath(`${path}${i}.${file_ext}`) });
        frameDecorationList.push(decType);
    }
    return frameDecorationList;
}

function themeToAnimationName(theme: vscode.ColorTheme): string {
    let animTheme = "dark";
    switch (theme.kind) {
        case vscode.ColorThemeKind.Dark:
        case vscode.ColorThemeKind.HighContrast:
            animTheme = "dark";
            break;
        case vscode.ColorThemeKind.Light:
        case vscode.ColorThemeKind.HighContrastLight:
            animTheme = "light";
            break;
        default:
            break;
    }
    return animTheme;
}
