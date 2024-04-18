
import * as vscode from "vscode";
import { LanguageClient } from "vscode-languageclient/node";
import { Manager, Observer } from "./Manager";


export type VerificationStatus = Array<[vscode.Range, boolean]>;

// Subject
export class VerificationManager extends Manager {

    private client: LanguageClient;

    private verificationStatus: VerificationStatus = [];



    constructor(client: LanguageClient) {
        super();
        this.client = client;
    }

    public getStatus(): VerificationStatus {
        return this.verificationStatus;
    }

    public setStatus(newStatus: VerificationStatus): void {
        this.verificationStatus = newStatus;
        this.notify(newStatus);
    }


    public async verify(editor: vscode.TextEditor, document: vscode.TextDocument): Promise<VerificationStatus> {
        let documentItem = {
            uri: document.uri.toString(),
            languageId: document.languageId,
            version: document.version,
            text: document.getText()
        }
        let response: VerificationStatus = await this.client.sendRequest('custom/verifyStatus', { text_document: documentItem });
        this.setStatus(response);
        return response;
    }

}

