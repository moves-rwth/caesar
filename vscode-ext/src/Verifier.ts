import { TextDocumentIdentifier } from "vscode-languageclient";
import { ExtensionContext, OutputChannel } from "vscode";
import { CaesarClient } from "./CaesarClient";
import { StatusBarComponent } from "./StatusBarComponent";
import { GutterStatusComponent } from "./GutterStatusComponent";
import { ComputedPreComponent } from "./ComputedPreComponent";
import * as vscode from 'vscode';
import { ServerInstaller } from "./ServerInstaller";

export class DocumentMap<T> {
    private map = new Map<string, [TextDocumentIdentifier, T]>();

    public insert(document_id: TextDocumentIdentifier, value: T) {
        this.map.set(document_id.uri.toString(), [document_id, value]);
    }

    public get(document_id: TextDocumentIdentifier): T | undefined {
        const res = this.map.get(document_id.uri.toString());
        if (res !== undefined) {
            return res[1];
        }
        return undefined;
    }

    public entries(): [TextDocumentIdentifier, T][] {
        return Array.from(this.map.values());
    }
}

export class Verifier {

    public context: ExtensionContext;
    public outputChannel: OutputChannel;
    public installer: ServerInstaller;
    public client: CaesarClient;
    private statusBar: StatusBarComponent;
    private gutterStatus: GutterStatusComponent;
    private displayComputedPre: ComputedPreComponent;

    constructor(context: ExtensionContext) {
        this.context = context;
        this.outputChannel = vscode.window.createOutputChannel("Caesar", "text");
        this.installer = new ServerInstaller(context, this);
        this.client = new CaesarClient(context, this.outputChannel, this.installer);
        this.statusBar = new StatusBarComponent(this);
        this.gutterStatus = new GutterStatusComponent(this);
        this.displayComputedPre = new ComputedPreComponent(this);
    }

    async start(recommendInstallation: boolean) {
        await this.client.start(recommendInstallation);
    }

}
