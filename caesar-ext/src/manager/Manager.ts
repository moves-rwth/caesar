// Parent class for Observer-pattern Subjects which we call Managers
export class Manager {
    // Observer-pattern subject

    private observers: Observer[] = []


    /// Notify the observers with the latest verification status
    public notify(update: any) {
        this.observers.forEach(observer => observer.receiveUpdate(update));
    }

    /// Subscribe an observer to the VerificationManager
    public subscribe(o: Observer) {
        if (this.observers.includes(o)) {
            return;
        }
        this.observers.push(o);
    }

    /// Subscribe multiple observers to the VerificationManager
    public subscribeMany(o: Array<Observer>) {
        o.forEach(observer => this.subscribe(observer));
    }

    /// Unsubscribe an observer from the VerificationManager
    public unsubscribe(o: Observer) {
        const index = this.observers.indexOf(o);
        if (index === -1) {
            return;
        }
        this.observers.splice(index, 1);
    }
}


export class Observer {

    private callback: (update: any) => void;
    private manager: Manager;
    private enabled: boolean = true;

    public constructor(manager: Manager, callback: (update: any) => void) {
        this.callback = callback;
        this.manager = manager;

        this.manager.subscribe(this);
    }


    public receiveUpdate(update: any): void {
        this.callback(update);
    }

    public disable() {
        if (!this.enabled) {
            return;
        }
        this.manager.unsubscribe(this);
    }

    public enable() {
        if (this.enabled) {
            return;
        }
        this.manager.subscribe(this);
    }
}




