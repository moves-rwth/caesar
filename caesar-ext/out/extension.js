"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.deactivate = exports.activate = void 0;
// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
const vscode = __importStar(require("vscode"));
const path = __importStar(require("path"));
const os = __importStar(require("os"));
const node_1 = require("vscode-languageclient/node");
let client;
// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
function activate(context) {
    let serverExecutable = "cargo";
    // If the extension is launched in debug mode then the debug server options are used
    // Otherwise the run options are used
    let serverOptions = {
        run: {
            command: serverExecutable,
            args: ['run', '--', '--language-server'],
            options: { cwd: path.resolve(os.homedir(), 'caesar') },
        },
        debug: {
            command: serverExecutable,
            args: ['run', '--', '--language-server'],
            options: { cwd: path.resolve(os.homedir(), 'caesar') },
        }
    };
    // Options to control the language client
    let clientOptions = {
        diagnosticCollectionName: 'caesar',
        // Register the server for heyvl documents
        documentSelector: [{ scheme: 'file', language: 'heyvl' }],
        synchronize: {
            // Notify the server about file changes to '.clientrc files contained in the workspace
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.heyvl')
        }
    };
    // Create the language client and start the client.
    client = new node_1.LanguageClient('caesar', 'Caesar', serverOptions, clientOptions);
    let decorationType = vscode.window.createTextEditorDecorationType({
        after: {
            color: new vscode.ThemeColor('editor.foreground'),
            backgroundColor: new vscode.ThemeColor('editor.background'),
        },
    });
    vscode.workspace.onDidSaveTextDocument(event => {
        const openEditor = vscode.window.visibleTextEditors.filter(editor => editor.document.uri === event.uri)[0];
        getProcStatus(openEditor, decorationType, openEditor.document);
    });
    // // Start the client. This will also launch the server
    client.start();
    // let editor = vscode.window.activeTextEditor;
    // if (editor) {
    // 	getProcStatus(editor, decorationType, editor.document);
    // }
    // // // Use the console to output diagnostic information (console.log) and errors (console.error)
    // // // This line of code will only be executed once when your extension is activated
    console.log('Congratulations, your extension "caesar" is now active!');
    // // The command has been defined in the package.json file
    // // Now provide the implementation of the command with registerCommand
    // // The commandId parameter must match the command field in package.json
    // let disposable = vscode.commands.registerCommand('caesar.helloWorld', () => {
    // 	// The code you place here will be executed every time your command is executed
    // 	// Display a message box to the user
    // 	vscode.window.showInformationMessage('Hello World from caesar!!!!');
    // });
    // context.subscriptions.push(disposable);
}
exports.activate = activate;
// This method is called when your extension is deactivated
function deactivate() { }
exports.deactivate = deactivate;
function updateDecorations(editor, decorationType, procStatus = []) {
    const decorations = [];
    // const procStaus = getProcStatus(editor.document);
    // Assuming `procedures` is an array of procedure positions
    for (const proc of procStatus) {
        const position = proc[0].start;
        const verified = proc[1];
        // Put the checkmark before the proc.
        const range = new vscode.Range(position, position);
        const decoration = {
            range,
            renderOptions: {
                after: {
                    contentText: verified ? '✔️' : '❌',
                    color: new vscode.ThemeColor('editor.foreground'),
                },
            },
        };
        decorations.push(decoration);
    }
    editor.setDecorations(decorationType, decorations);
}
async function getProcStatus(editor, decorationType, document) {
    let documentItem = {
        uri: document.uri.toString(),
        languageId: document.languageId,
        version: document.version,
        text: document.getText()
    };
    let response = await client.sendRequest('custom/verifyStatus', { text_document: documentItem });
    updateDecorations(editor, decorationType, response);
}
//# sourceMappingURL=extension.js.map