
import * as vscode from "vscode";
import { LanguageClient } from "vscode-languageclient/node";
import { Manager, Observer } from "./Manager";


export enum State {
    Starting,
    Ready,
    FailedToStart,
    Verifying,
    Finished,
}


// Subject
export class StateManager extends Manager {

    private client: LanguageClient;

    private state: State = State.Starting;

    constructor(client: LanguageClient) {
        super();
        this.client = client;

        client.onNotification("custom/serverReady", () => {
            this.setState(State.Ready);
        })
    }


    public setState(state: State) {
        this.state = state;
        this.notify(state);
    }

    public getState(): State {
        return this.state;
    }

}



