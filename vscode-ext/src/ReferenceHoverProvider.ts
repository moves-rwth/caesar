import * as vscode from 'vscode';
import { findReferenceToken, HeyVlGrammar } from './HeyVlGrammar';
import { HEYVL_REFERENCE, ReferenceEntry } from './HeyVlReference';

export function renderReference(entry: ReferenceEntry): vscode.MarkdownString {
    const markdown = new vscode.MarkdownString();
    markdown.appendMarkdown(`**${entry.title}**\n\n${entry.description}`);
    if (entry.details) {
        markdown.appendMarkdown(`\n\n${entry.details}`);
    }
    if (entry.example) {
        markdown.appendMarkdown('\n\n');
        markdown.appendCodeblock(entry.example, 'heyvl');
    }
    markdown.appendMarkdown(`\n\n[Documentation](${entry.documentation})`);
    return markdown;
}

export class ReferenceHoverProvider implements vscode.HoverProvider {
    constructor(private readonly grammar: HeyVlGrammar) { }

    async provideHover(document: vscode.TextDocument, position: vscode.Position, cancellation: vscode.CancellationToken): Promise<vscode.Hover | undefined> {
        if (document.languageId !== 'heyvl' || cancellation.isCancellationRequested) {
            return undefined;
        }
        const version = document.version;
        const grammar = await this.grammar.getGrammar();
        if (cancellation.isCancellationRequested || version !== document.version) {
            return undefined;
        }
        const token = findReferenceToken(grammar, document.getText(), document.offsetAt(position));
        if (!token) {
            return undefined;
        }
        const range = new vscode.Range(document.positionAt(token.start), document.positionAt(token.end));
        return new vscode.Hover(renderReference(HEYVL_REFERENCE[token.key]), range);
    }
}

export function registerReferenceHovers(extensionPath: string): vscode.Disposable {
    const grammar = new HeyVlGrammar(extensionPath);
    return vscode.Disposable.from(
        grammar,
        vscode.languages.registerHoverProvider({ language: 'heyvl' }, new ReferenceHoverProvider(grammar)),
    );
}
