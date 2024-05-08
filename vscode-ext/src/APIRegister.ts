import * as vscode from 'vscode';

export const registerFunctions: { [K: string]: Function } = {
    "onDidChangeConfiguration": vscode.workspace.onDidChangeConfiguration,
    "onDidChangeTextDocument": vscode.workspace.onDidChangeTextDocument,
    "onDidSaveTextDocument": vscode.workspace.onDidSaveTextDocument,
}

export type RegisterType = keyof typeof registerFunctions;

export default class APIRegister {

    /// Store all registered callbacks in a map to submit them to vscode api later
    private static callbackMap = new Map<RegisterType, Array<(...args: any[]) => void>>();


    /// Register a callback to be called when the vscode api event is triggered
    public static register(type: RegisterType, callback: (...args: any[]) => void): void {
        this.callbackMap.has(type) ? this.callbackMap.get(type)?.push(callback) : this.callbackMap.set(type, [callback]);
    }

    /// Submit all registered callbacks to vscode api
    public static submitAll(): void {

        for (const type of this.callbackMap.keys()) {
            if (registerFunctions[type] === undefined) {
                throw new Error(`The type ${type} is not a valid registration type`);
            }

            // All callbacks that we want to register to the specific event from vscode api
            const callbackList = this.callbackMap.get(type)!;

            // Collect all the callbacks into one function
            const totalCallback = (...args: any[]) => { callbackList.forEach((callback) => callback(...args)) };

            // Register the function to the vscode api by calling the corresponding event registration function
            registerFunctions[type](totalCallback);
        }

    }

}
