import * as vscode from 'vscode';
import { ConfigurationTarget } from 'vscode';

const CAESAR_CONFIG_SECTION = 'caesar';

function joinPath(...segments: (string | undefined)[]): string | undefined {
    const res = segments.filter((value) => value !== undefined);
    if (res.length === 0) {
        return undefined;
    } else {
        return res.join(".");
    }
}

export class ConfigCategory {
    private name?: string;

    constructor(name: string | undefined, parent?: ConfigCategory) {
        this.name = joinPath(parent?.name, name);
    }

    private getLocalPath(key: string): string {
        const res = joinPath(this.name, key);
        if (res === undefined) {
            throw new Error("unreachable");
        }
        return res;
    }

    public isAffected(event: vscode.ConfigurationChangeEvent): boolean {
        const path = joinPath(CAESAR_CONFIG_SECTION, this.name);
        if (path === undefined) {
            throw new Error("unreachable");
        }
        return event.affectsConfiguration(path);
    }

    public get(key: string): any {
        const path = this.getLocalPath(key);
        const val = vscode.workspace.getConfiguration(CAESAR_CONFIG_SECTION).get(path);
        if (val === undefined) {
            throw new Error(`${key} is not defined in the configuration file`);
        }
        return val;
    }

    public async update(key: string, value: any) {
        const config = vscode.workspace.getConfiguration(CAESAR_CONFIG_SECTION);
        const target = vscode.workspace.workspaceFolders ? ConfigurationTarget.Workspace : ConfigurationTarget.Global;
        const path = this.getLocalPath(key);
        await config.update(path, value, target);
    }

    public child(key: string): ConfigCategory {
        return new ConfigCategory(key, this);
    }

}

// Configurations
// ------------------------------------------------

// Root Configurations:

export const CaesarConfig = new ConfigCategory(undefined);

export const ViewConfig = new ConfigCategory("userInterface");
export const ServerConfig = new ConfigCategory("server");
export const InstallerConfig = new ConfigCategory("installer");

// View Configurations:

export const GutterInformationViewConfig = ViewConfig.child('gutterIcons');
export const StatusBarViewConfig = ViewConfig.child('statusBar');
export const InlineGhostTextViewConfig = ViewConfig.child('inlineGhostText');
