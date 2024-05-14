import * as vscode from 'vscode';

export const CONFIGURATION_SECTION = 'caesar';

export default class Configuration {

    /// Get a configuration value from the configuration file with the given key
    public static get(key: string): any {
        const val = vscode.workspace.getConfiguration(CONFIGURATION_SECTION).get(key)
        if (val === undefined) {
            throw new Error(`${key} is not defined in the configuration file`);
        }
        return val;
    }

}

export class ConfigCategory {
    public name: string;
    private parent: ConfigCategory | null;


    constructor(name: string, parent: ConfigCategory | null,) {
        this.name = name;
        this.parent = parent;
    }

    /// Construct the path of the category based on its hiearchical position
    public getPath(): string {
        return this.parent ? this.parent.getPath() + "." + this.name : this.name;
    }

    public get(key: string): any {
        return Configuration.get(this.getPath() + "." + key);
    }

}

// Configurations
// ------------------------------------------------

// Root Configurations:

export const ViewConfig = new ConfigCategory("uI", null);
export const ServerConfig = new ConfigCategory("server", null);

// View Configurations:

export const GutterInformationViewConfig = new ConfigCategory('gutterIcons', ViewConfig);
export const StatusBarViewConfig = new ConfigCategory('statusBar', ViewConfig);
export const InlineGhostTextViewConfig = new ConfigCategory('inlineGhostText', ViewConfig);
