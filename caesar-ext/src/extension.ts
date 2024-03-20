// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';

// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {


	let decorationType = vscode.window.createTextEditorDecorationType({
		after: {
			color: new vscode.ThemeColor('editor.foreground'),
			backgroundColor: new vscode.ThemeColor('editor.background'),
		},
	});

	let editor = vscode.window.activeTextEditor;
	if (editor) {
		updateDecorations(editor, decorationType);
	}

	vscode.workspace.onWillSaveTextDocument(event => {
		const openEditor = vscode.window.visibleTextEditors.filter(
			editor => editor.document.uri === event.document.uri
		)[0]
		updateDecorations(openEditor, decorationType)
	})

	// Use the console to output diagnostic information (console.log) and errors (console.error)
	// This line of code will only be executed once when your extension is activated
	console.log('Congratulations, your extension "caesar" is now active!');

	// The command has been defined in the package.json file
	// Now provide the implementation of the command with registerCommand
	// The commandId parameter must match the command field in package.json
	let disposable = vscode.commands.registerCommand('caesar.helloWorld', () => {
		// The code you place here will be executed every time your command is executed
		// Display a message box to the user
		vscode.window.showInformationMessage('Hello World from caesar!!!!');
	});

	context.subscriptions.push(disposable);
}

// This method is called when your extension is deactivated
export function deactivate() { }

function updateDecorations(editor: vscode.TextEditor, decorationType: vscode.TextEditorDecorationType) {
	const decorations: vscode.DecorationOptions[] = [];
	const procedures = [new vscode.Position(0, 0)];
	// Assuming `procedures` is an array of procedure positions
	for (const position of procedures) {
		const verified = isVerified(editor.document, position);
		const range = new vscode.Range(position, position.translate(0, 0));
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

function isVerified(document: vscode.TextDocument, position: vscode.Position): boolean {
	// Implement logic to determine if the procedure at the given position is verified
	return true; // Return true if verified, false otherwise
}
