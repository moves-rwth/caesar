import { TextDocumentIdentifier } from "vscode-languageclient";
import { ExtensionContext } from "vscode";
import { CaesarClient } from "./CaesarClient";
import { StatusBarComponent } from "./StatusBarComponent";
import { GutterStatusComponent } from "./GutterStatusComponent";
import { ComputedPreComponent } from "./ComputedPreComponent";

export class DocumentMap<T> {
    private map: Map<string, [TextDocumentIdentifier, T]> = new Map();

    public insert(document_id: TextDocumentIdentifier, value: T) {
        this.map.set(document_id.uri.toString(), [document_id, value]);
    }

    public get(document_id: TextDocumentIdentifier): T | undefined {
        let res = this.map.get(document_id.uri.toString());
        if (res !== undefined) {
            return res[1];
        }
        return undefined;
    }

    public entries(): Array<[TextDocumentIdentifier, T]> {
        return Array.from(this.map.values());
    }
}

export class Verifier {

    public context: ExtensionContext;
    public client: CaesarClient;
    private statusBar: StatusBarComponent;
    private gutterStatus: GutterStatusComponent;
    private displayComputedPre: ComputedPreComponent;

    constructor(context: ExtensionContext) {
        this.context = context;
        this.client = new CaesarClient(context);
        this.statusBar = new StatusBarComponent(this);
        this.gutterStatus = new GutterStatusComponent(this);
        this.displayComputedPre = new ComputedPreComponent(this);
    }

    async start() {
        await this.client.start();
    }

}
