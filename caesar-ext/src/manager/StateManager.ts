
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

    private state: State;

    constructor(client: LanguageClient) {
        super();
        this.client = client;
        this.state = State.Starting;
        this.notify(this.state);

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



