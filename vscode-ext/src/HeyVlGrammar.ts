import { readFile } from 'node:fs/promises';
import { join } from 'node:path';
import { createOnigScanner, createOnigString, loadWASM } from 'vscode-oniguruma';
import { IGrammar, INITIAL, parseRawGrammar, Registry } from 'vscode-textmate';
import { HEYVL_REFERENCE } from './HeyVlReference';

/** Loads the same grammar used by syntax highlighting, once and on demand. */
export class HeyVlGrammar {
    private registry?: Registry;
    private loading?: Promise<IGrammar>;

    constructor(private readonly extensionPath: string) { }

    getGrammar(): Promise<IGrammar> {
        return this.loading ??= this.load();
    }

    private async load(): Promise<IGrammar> {
        const wasm = await readFile(join(this.extensionPath, 'dist/onig.wasm'));
        await loadWASM(new Uint8Array(wasm).buffer);
        const grammarPath = join(this.extensionPath, 'heyvl/heyvl.tmLanguage.json');
        this.registry = new Registry({
            onigLib: Promise.resolve({ createOnigScanner, createOnigString }),
            loadGrammar: async scope => scope === 'source.heyvl'
                ? parseRawGrammar(await readFile(grammarPath, 'utf8'), grammarPath)
                : null,
        });
        const grammar = await this.registry.loadGrammar('source.heyvl');
        if (!grammar) {
            throw new Error('Could not load the HeyVL syntax grammar.');
        }
        return grammar;
    }

    dispose(): void {
        this.registry?.dispose();
    }
}

export interface ReferenceToken {
    readonly key: string;
    /** UTF-16 offsets, as used by VS Code's TextDocument. */
    readonly start: number;
    readonly end: number;
}

// The grammar already groups composite forms into one token.
// Ignore horizontal whitespace on both sides of this lookup, so `@ wp`, `! ?`, and `if⊓` need no separate parsing rules here.
// Returned ranges still cover the original text.
const referenceKeys = new Map(Object.keys(HEYVL_REFERENCE).map(key => [withoutSpacing(key), key]));

function withoutSpacing(spelling: string): string {
    return spelling.replace(/[ \t]+/g, '');
}

/** Find the reference entry for a token from the shared highlighting grammar. */
export function findReferenceToken(grammar: IGrammar, source: string, offset: number): ReferenceToken | undefined {
    if (!source.length || offset < 0 || offset > source.length) {
        return undefined;
    }
    // Keyboard Show Hover can query the caret just after the final token.
    // Everywhere else, use normal half-open token ranges [start, end).
    const lookupOffset = offset === source.length ? offset - 1 : offset;
    let state = INITIAL;
    let lineStart = 0;
    // Tokenize the prefix, not just the hovered line: TextMate's rule stack carries multiline strings and nested comments into subsequent lines.
    // Splitting on LF retains CR in CRLF files, preserving UTF-16 offsets.
    for (const line of source.split('\n')) {
        const result = grammar.tokenizeLine(line, state);
        state = result.ruleStack;
        if (lookupOffset > lineStart + line.length) {
            lineStart += line.length + 1;
            continue;
        }

        const column = lookupOffset - lineStart;
        // TextMate appends a synthetic newline; exclude it from hover ranges.
        const token = result.tokens.find(candidate =>
            candidate.startIndex <= column && column < Math.min(candidate.endIndex, line.length));
        // A word in a comment or string can still exactly match a catalog key.
        if (!token || token.scopes.some(scope => scope.startsWith('comment.') || scope.startsWith('string.'))) {
            return undefined;
        }
        const start = lineStart + token.startIndex;
        const end = lineStart + Math.min(token.endIndex, line.length);
        const key = referenceKeys.get(withoutSpacing(source.slice(start, end)));
        return key === undefined ? undefined : { key, start, end };
    }
    return undefined;
}
