// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import * as path from 'path';
import * as os from 'os';
import { LanguageClient, LanguageClientOptions, ServerOptions, TransportKind } from 'vscode-languageclient/node';


let client: LanguageClient;
// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {

	let serverExecutable = "cargo"

	// If the extension is launched in debug mode then the debug server options are used
	// Otherwise the run options are used
	let serverOptions: ServerOptions = {
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
	let clientOptions: LanguageClientOptions = {
		diagnosticCollectionName: 'caesar',
		// Register the server for heyvl documents
		documentSelector: [{ scheme: 'file', language: 'heyvl' }],
		synchronize: {
			// Notify the server about file changes to '.clientrc files contained in the workspace
			fileEvents: vscode.workspace.createFileSystemWatcher('**/*.heyvl')
		}
	};

	// Create the language client and start the client.
	client = new LanguageClient(
		'caesar',
		'Caesar',
		serverOptions,
		clientOptions
	);


	let decorationType = vscode.window.createTextEditorDecorationType({
		after: {
			color: new vscode.ThemeColor('editor.foreground'),
			backgroundColor: new vscode.ThemeColor('editor.background'),
		},

	});

	vscode.workspace.onDidSaveTextDocument(event => {
		const openEditor = vscode.window.visibleTextEditors.filter(
			editor => editor.document.uri === event.uri
		)[0]
		getProcStatus(openEditor, decorationType, openEditor.document);
	})



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

// This method is called when your extension is deactivated
export function deactivate() { }

function updateDecorations(editor: vscode.TextEditor, decorationType: vscode.TextEditorDecorationType, procStatus: Array<[vscode.Range, boolean]> = []) {
	const decorations: vscode.DecorationOptions[] = [];
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


async function getProcStatus(editor: vscode.TextEditor, decorationType: vscode.TextEditorDecorationType, document: vscode.TextDocument) {

	let documentItem = {
		uri: document.uri.toString(),
		languageId: document.languageId,
		version: document.version,
		text: document.getText()
	}
	let response: Array<[vscode.Range, boolean]> = await client.sendRequest('custom/verifyStatus', { text_document: documentItem });
	updateDecorations(editor, decorationType, response);
}
