import * as vscode from 'vscode';

const CONFIGURATION_SECTION = 'caesar';

export default class Configuration {
    /// Get a configuration value from the configuration file with the given key    
    protected static getConfiguration(key: string): any {
        const val: any | undefined = vscode.workspace.getConfiguration(CONFIGURATION_SECTION).get(key)
        if (val === undefined) {
            throw new Error(`${key} is not defined in the configuration file`);
        }
        return val;
    }

    protected static getConfigurationPath(): string {
        return "caesar."
    }

}
