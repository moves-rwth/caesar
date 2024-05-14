// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import { Verifier } from './Verifier';
import { ServerConfig } from './Configuration';
import { ConfigurationConstants } from './constants';

// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
	let verifier = new Verifier(context);
	if (ServerConfig.get(ConfigurationConstants.autoStartServer)) {
		verifier.start();
	}
}

// This method is called when the extension is deactivated
export function deactivate() { }

