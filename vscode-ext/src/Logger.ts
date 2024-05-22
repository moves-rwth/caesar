import { OutputChannel, window } from "vscode";

/**
 * Our own custom logger. This is very similar to VSCode's LogOutputChannel, but
 * doesn't automatically preprend times to everything that's printed via the
 * OutputChannel. This is useful because otherwise we get duplicate timestamps
 * from the server and the client.
 */
export default class Logger {
    public outputChannel: OutputChannel;

    public constructor() {
        this.outputChannel = window.createOutputChannel("Caesar", "text");
    }

    private printTimedMessage(level: string, message: string, data: any[]) {
        const time = new Date().toLocaleTimeString();
        const prefix = `[${level} - ${time}]`;
        const line = [prefix, message].concat(data).join(" ");
        this.outputChannel.appendLine(line);
    }

    public error(message: string, ...data: any[]) {
        this.printTimedMessage("Error", message, data);
    }

    public info(message: string, ...data: any[]) {
        this.printTimedMessage("Info", message, data);
    }
}