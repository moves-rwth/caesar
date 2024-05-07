
import * as vscode from "vscode";
import { LanguageClient } from "vscode-languageclient/node";
import { Manager, Observer } from "./Manager";
import APIRegister from "../APIRegister";


export type VerificationStatus = Array<[vscode.Range, boolean]>;

export class VerificationManager extends Manager {

    private client: LanguageClient;

    // private verificationStatus: Map<vscode.TextEditor, VerificationStatus> = new Map();
    private verificationStatus: VerificationStatus = [];

    constructor(client: LanguageClient) {
        super();
        this.client = client;

    }

    public getStatus(editor: vscode.TextEditor): VerificationStatus {
        // return this.verificationStatus.get(editor) || [];
        return this.verificationStatus;
    }

    public setStatus(editor: vscode.TextEditor, newStatus: VerificationStatus): void {
        // this.verificationStatus.set(editor, newStatus);
        this.verificationStatus = newStatus;
        this.notify(this.verificationStatus);
    }


    public async verify(editor: vscode.TextEditor, document: vscode.TextDocument): Promise<VerificationStatus> {
        let documentItem = {
            uri: document.uri.toString(),
            languageId: document.languageId,
            version: document.version,
            text: document.getText()
        }
        let response: VerificationStatus = await this.client.sendRequest('custom/verifyStatus', { text_document: documentItem });
        this.setStatus(editor, response);
        return response;
    }

}

