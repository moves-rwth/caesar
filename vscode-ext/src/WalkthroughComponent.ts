import { ExtensionContext, ViewColumn, commands, window, workspace } from "vscode";

export class WalkthroughComponent {
    private context: ExtensionContext;

    constructor(context: ExtensionContext) {
        this.context = context;

        workspace.onDidOpenTextDocument(async (document) => {
            if (document.languageId === 'heyvl') {
                await this.setOpenedHeyVl(true);
            }
        });

        this.context.subscriptions.push(commands.registerCommand('caesar.openExampleFileBeside', async () => {
            await this.openExampleFile();
        }));

        this.context.subscriptions.push(commands.registerCommand('caesar.openWalkthrough', async () => {
            await this.showWalkthrough();
        }));

        const shownWalkthrough: boolean = this.context.globalState.get("shownWalkthrough", false);
        if (!shownWalkthrough) {
            void this.showWalkthrough();
        }
    }

    private async showWalkthrough() {
        await commands.executeCommand('workbench.action.openWalkthrough', 'rwth-moves.caesar#caesar.welcome');
        await this.context.globalState.update("shownWalkthrough", true);
    }

    public async setBinaryInstalled(done: boolean) {
        await commands.executeCommand('setContext', 'caesarverifier.installedBinary', done);
    }

    public async setOpenedHeyVl(done: boolean) {
        await commands.executeCommand('setContext', 'caesarverifier.openedHeyVl', done);
    }

    public async setVerifiedHeyVL(done: boolean) {
        await this.setBinaryInstalled(true);
        await this.setOpenedHeyVl(true);
        await commands.executeCommand('setContext', 'caesarverifier.verifiedHeyVl', done);
    }

    public async setExplainedVc(done: boolean) {
        await commands.executeCommand('setContext', 'caesarverifier.explainedVc', done);
    }

    private async openExampleFile() {
        const content = `// save as geo.heyvl

coproc geo(init_c: UInt) -> (c: UInt)
    pre init_c + 1
    post c
{
    c = init_c
    var cont: Bool = true
    @invariant(ite(cont, c + 1, c))
    while cont {
        var prob_choice: Bool = flip(0.5)
        if prob_choice {
            c = c + 1
        } else {
            cont = false
        }
    }
}`;
        const document = await workspace.openTextDocument({
            language: "heyvl",
            content,
        });
        await window.showTextDocument(document, ViewColumn.Beside);
    }
}