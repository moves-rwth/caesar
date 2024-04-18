// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import * as path from 'path';
import * as os from 'os';
import { LanguageClient, LanguageClientOptions, ServerOptions, TransportKind } from 'vscode-languageclient/node';
import { VerificationManager } from './VerificationManager';
import { GutterInformationView } from './GutterInformationView';
import { StatusBarView } from './StatusBarView';
import { State, StateManager } from './StateManager';


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


	// Initialize Managers
	let verificationManager = new VerificationManager(client);
	let stateManager = new StateManager(client);

	// Initialize UI Views
	let gutterInfo = new GutterInformationView(verificationManager, context);
	let statusBar = new StatusBarView(stateManager);


	vscode.workspace.onDidSaveTextDocument(event => {
		if (stateManager.getState() === State.Starting) {
			return
		}
		const openEditor = vscode.window.visibleTextEditors.filter(
			editor => editor.document.uri === event.uri
		)[0]
		stateManager.setState(State.Verifying);
		console.log("Verification Started")
		verificationManager.verify(openEditor, openEditor.document).then((_) => {
			stateManager.setState(State.Finished)
		}
		)


	});

	// Start the client. This will also launch the server
	client.start();

	console.log('Caesar is now active!');

	context.subscriptions.push(statusBar);
	context.subscriptions.push(gutterInfo);
	context.subscriptions.push(client);

}

// This method is called when the extension is deactivated
export function deactivate() { }

