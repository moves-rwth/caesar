
import * as vscode from "vscode";
import { LanguageClient, VersionedTextDocumentIdentifier } from "vscode-languageclient/node";
import { Manager, Observer } from "./Manager";
import APIRegister from "../APIRegister";


export type VerificationStatus = {
    document: VersionedTextDocumentIdentifier,
    statuses: Array<[vscode.Range, boolean]>,
};

export class VerificationManager extends Manager {

    private client: LanguageClient;


    constructor(client: LanguageClient) {
        super();
        this.client = client;
    }

    public async verify(editor: vscode.TextEditor, document: vscode.TextDocument): Promise<void> {
        let documentItem = {
            uri: document.uri.toString(),
            languageId: document.languageId,
            version: document.version,
            text: document.getText()
        }
        await this.client.sendRequest('custom/verifyStatus', { text_document: documentItem });
    }

}

