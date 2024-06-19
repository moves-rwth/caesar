import { parse, SemVer } from "semver";
import { ExtensionContext } from "vscode";
import * as os from 'os';
import Logger from "./Logger";

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

export function getPlatformAssetFilter(logger: Logger): string | null {
    const platform = os.platform();
    const arch = os.arch();
    switch (platform) {
        case "linux":
            if (arch === "x64") {
                return "x86_64-unknown-linux";
            } else {
                return null;
            }
        case "win32":
            if (arch === "x64") {
                return "x86_64-pc-windows";
            } else {
                return null;
            }
        case "darwin":
            if (arch === "x64") {
                return "x86_64-apple-darwin";
            } else if (arch === "arm64") {
                return "aarch64-apple-darwin";
            } else {
                return null;
            }
        default:
            logger.error(`Unsupported platform: ${platform}`);
            return null;
    }
}

export function getPlatformAssetExecutableName(): string | null {
    const platform = os.platform();
    switch (platform) {
        case "linux":
        case "darwin":
            return "caesar";
        case "win32":
            return "caesar.exe";
        default:
            console.log(`Unsupported platform: ${platform}`);
            return null;
    }
}
