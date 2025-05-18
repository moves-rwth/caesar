import { TextDocumentIdentifier } from "vscode-languageclient";
import { ExtensionContext, commands } from "vscode";
import { CaesarClient } from "./CaesarClient";
import { StatusBarComponent } from "./StatusBarComponent";
import { GutterStatusComponent } from "./GutterStatusComponent";
import { ComputedPreComponent } from "./ComputedPreComponent";
import { ServerInstaller } from "./ServerInstaller";
import { WalkthroughComponent } from "./WalkthroughComponent";
import Logger from "./Logger";
import { getExtensionVersion } from "./version";

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

    public remove(document_id: TextDocumentIdentifier) {
        this.map.delete(document_id.uri.toString());
    }
}

export class Verifier {

    public context: ExtensionContext;
    public logger: Logger;
    public walkthrough: WalkthroughComponent;
    public installer: ServerInstaller;
    public client: CaesarClient;
    private statusBar: StatusBarComponent;
    private gutterStatus: GutterStatusComponent;
    private displayComputedPre: ComputedPreComponent;

    constructor(context: ExtensionContext) {
        this.context = context;

        this.logger = new Logger();
        context.subscriptions.push(commands.registerCommand('caesar.showOutput', () => {
            this.logger.show();
        }));

        const version = getExtensionVersion(context);
        this.logger.info(`Starting Caesar for VSCode ${version.toString()}.`);

        this.walkthrough = new WalkthroughComponent(context);
        this.installer = new ServerInstaller(context, this);
        this.client = new CaesarClient(context, this.logger, this.walkthrough, this.installer);
        this.statusBar = new StatusBarComponent(this);
        this.gutterStatus = new GutterStatusComponent(this);
        this.displayComputedPre = new ComputedPreComponent(this);
    }

    async start(recommendInstallation: boolean) {
        await this.client.start(recommendInstallation);
    }

}
