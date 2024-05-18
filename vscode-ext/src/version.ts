import { parse, SemVer } from "semver";
import { ExtensionContext } from "vscode";

export function getExtensionVersion(context: ExtensionContext): SemVer {
    // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access
    const packageVersion: string = context.extension.packageJSON["version"];
    const res = parse(packageVersion);
    if (!res) {
        throw new Error("could not parse extension version");
    }
    return res;
}

export function isPatchCompatible(a: SemVer, b: SemVer): boolean {
    return a.major === b.major && a.minor === b.minor;
}
