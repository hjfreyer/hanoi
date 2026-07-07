import { MachineSpec, transition, isCompleted } from "./spec";

export type Machine = (ctx: MachineContext) => Promise<void>;

export interface MachineContext {
    read(channel: string[]): Promise<any>;
    write(channel: string[], value: any): Promise<void>;
    select<T>(cases: SelectCase<T>[]): Promise<T>;
    spawn(key: string, machine: Machine): void;
}

export type SelectCase<T> =
    | { kind: "read"; channel: string[]; callback: (value: any) => T }
    | { kind: "write"; channel: string[]; value: any; callback: () => T };

interface PendingOp {
    kind: "read" | "write";
    absoluteChannel: string[];
    value?: any;
    transaction?: SelectTransaction;
    resolve: (val: any) => void;
    alreadyTransitioned: boolean;
}

interface SelectTransaction {
    resolved: boolean;
    cleanup?: () => void;
}

interface ExternalWriter {
    value: any;
    resolve: () => void;
}

interface ExternalReader {
    resolve: (val: any) => void;
}

export class Runtime {
    private spec: MachineSpec;
    private activeTasks = 0;
    
    // Canonical channel map for wires
    private wires = new Map<string, string>();
    
    // Queues of pending machine operations
    private pendingReaders = new Map<string, PendingOp[]>();
    private pendingWriters = new Map<string, PendingOp[]>();
    
    // Queues of pending external operations
    private pendingExternalWriters = new Map<string, ExternalWriter[]>();
    private pendingExternalReaders = new Map<string, ExternalReader[]>();

    private resolveRun?: () => void;
    private rejectRun?: (err: Error) => void;
    private checkStatusDeferred = false;
    private hasFailed = false;

    constructor(initialSpec: MachineSpec, private mainMachine: Machine) {
        this.spec = initialSpec;
    }

    wire(pathA: string[], pathB: string[]): void {
        const keyA = pathA.join(".");
        const keyB = pathB.join(".");
        const canonicalA = this.getCanonicalChannel(keyA);
        const canonicalB = this.getCanonicalChannel(keyB);
        if (canonicalA !== canonicalB) {
            this.wires.set(canonicalA, canonicalB);
        }
    }

    run(): Promise<void> {
        return new Promise<void>((resolve, reject) => {
            this.resolveRun = resolve;
            this.rejectRun = reject;
            
            // Start the main machine
            this.runTask(this.mainMachine(this.createContext([])));
        });
    }

    async externalWrite(channel: string[], value: any): Promise<void> {
        if (this.hasFailed) {
            throw new Error("Runtime has already failed");
        }
        
        const canonicalKey = this.getCanonicalChannel(channel.join("."));
        
        // Check if there is a pending machine reader
        const machineReader = this.popPendingReader(canonicalKey);
        if (machineReader) {
            try {
                const rChan = machineReader.alreadyTransitioned ? undefined : machineReader.absoluteChannel;
                this.transitionSpec(undefined, rChan);
            } catch (err) {
                this.fail(err as Error);
                throw err;
            }
            machineReader.resolve(value);
            return;
        }

        // Otherwise queue external writer
        return new Promise<void>((resolve) => {
            if (!this.pendingExternalWriters.has(canonicalKey)) {
                this.pendingExternalWriters.set(canonicalKey, []);
            }
            this.pendingExternalWriters.get(canonicalKey)!.push({ value, resolve });
            this.checkStatus();
        });
    }

    async externalRead(channel: string[]): Promise<any> {
        if (this.hasFailed) {
            throw new Error("Runtime has already failed");
        }
        
        const canonicalKey = this.getCanonicalChannel(channel.join("."));
        
        // Check if there is a pending machine writer
        const machineWriter = this.popPendingWriter(canonicalKey);
        if (machineWriter) {
            try {
                const wChan = machineWriter.alreadyTransitioned ? undefined : machineWriter.absoluteChannel;
                this.transitionSpec(wChan, undefined);
            } catch (err) {
                this.fail(err as Error);
                throw err;
            }
            machineWriter.resolve(undefined);
            return machineWriter.value;
        }

        // Otherwise queue external reader
        return new Promise<any>((resolve) => {
            if (!this.pendingExternalReaders.has(canonicalKey)) {
                this.pendingExternalReaders.set(canonicalKey, []);
            }
            this.pendingExternalReaders.get(canonicalKey)!.push({ resolve });
            this.checkStatus();
        });
    }

    private getCanonicalChannel(channelKey: string): string {
        let curr = channelKey;
        while (this.wires.has(curr)) {
            curr = this.wires.get(curr)!;
        }
        return curr;
    }

    private runTask(promise: Promise<void>) {
        this.activeTasks++;
        promise.then(
            () => {
                this.activeTasks--;
                this.checkStatus();
            },
            (err) => {
                this.activeTasks--;
                this.fail(err);
            }
        );
    }

    private fail(err: Error) {
        if (this.hasFailed) return;
        this.hasFailed = true;
        this.rejectRun?.(err);
    }

    private checkStatus() {
        if (this.checkStatusDeferred) return;
        this.checkStatusDeferred = true;
        Promise.resolve().then(() => {
            this.checkStatusDeferred = false;
            this.doCheckStatus();
        });
    }

    private doCheckStatus() {
        if (this.hasFailed) return;
        if (this.activeTasks > 0) return;

        const allCompleted = isCompleted(this.spec);
        
        let hasPendingInternal = false;
        for (const ops of this.pendingReaders.values()) {
            if (ops.length > 0) hasPendingInternal = true;
        }
        for (const ops of this.pendingWriters.values()) {
            if (ops.length > 0) hasPendingInternal = true;
        }

        if (allCompleted && !hasPendingInternal) {
            this.resolveRun?.();
            return;
        }
    }

    private createContext(prefix: string[]): MachineContext {
        const self = this;
        return {
            read(channel) {
                return this.select([{
                    kind: "read",
                    channel,
                    callback: (v) => v
                }]);
            },
            write(channel, value) {
                return this.select([{
                    kind: "write",
                    channel,
                    value,
                    callback: () => {}
                }]);
            },
            spawn(key, machine) {
                self.runTask(machine(self.createContext([...prefix, key])));
            },
            select(cases) {
                return self.executeSelect(prefix, cases);
            }
        };
    }

    private executeSelect<T>(prefix: string[], cases: SelectCase<T>[]): Promise<T> {
        if (this.hasFailed) {
            return Promise.reject(new Error("Runtime has already failed"));
        }

        const resolvedCases = cases.map(c => {
            if (c.kind === "read") {
                return {
                    kind: "read" as const,
                    absoluteChannel: [...prefix, ...c.channel],
                    callback: c.callback,
                    alreadyTransitioned: cases.length === 1
                };
            } else {
                return {
                    kind: "write" as const,
                    absoluteChannel: [...prefix, ...c.channel],
                    value: c.value,
                    callback: c.callback,
                    alreadyTransitioned: cases.length === 1
                };
            }
        });

        // If single case, transition immediately on initiation
        if (resolvedCases.length === 1) {
            const c = resolvedCases[0];
            try {
                if (c.kind === "read") {
                    this.transitionSpec(undefined, c.absoluteChannel);
                } else {
                    this.transitionSpec(c.absoluteChannel, undefined);
                }
            } catch (err) {
                this.fail(err as Error);
                return Promise.reject(err);
            }
        }

        // 1. Check for immediate match
        for (const c of resolvedCases) {
            const canonicalKey = this.getCanonicalChannel(c.absoluteChannel.join("."));
            if (c.kind === "read") {
                const machineWriter = this.popPendingWriter(canonicalKey);
                if (machineWriter) {
                    try {
                        const wChan = machineWriter.alreadyTransitioned ? undefined : machineWriter.absoluteChannel;
                        const rChan = c.alreadyTransitioned ? undefined : c.absoluteChannel;
                        this.transitionSpec(wChan, rChan);
                    } catch (err) {
                        this.fail(err as Error);
                        return Promise.reject(err);
                    }
                    machineWriter.resolve(undefined);
                    return Promise.resolve(c.callback(machineWriter.value));
                }
                const extWriter = this.popExternalWriter(canonicalKey);
                if (extWriter) {
                    try {
                        const rChan = c.alreadyTransitioned ? undefined : c.absoluteChannel;
                        this.transitionSpec(undefined, rChan);
                    } catch (err) {
                        this.fail(err as Error);
                        return Promise.reject(err);
                    }
                    extWriter.resolve();
                    return Promise.resolve(c.callback(extWriter.value));
                }
            } else { // write
                const machineReader = this.popPendingReader(canonicalKey);
                if (machineReader) {
                    try {
                        const wChan = c.alreadyTransitioned ? undefined : c.absoluteChannel;
                        const rChan = machineReader.alreadyTransitioned ? undefined : machineReader.absoluteChannel;
                        this.transitionSpec(wChan, rChan);
                    } catch (err) {
                        this.fail(err as Error);
                        return Promise.reject(err);
                    }
                    machineReader.resolve(c.value);
                    return Promise.resolve(c.callback());
                }
                const extReader = this.popExternalReader(canonicalKey);
                if (extReader) {
                    try {
                        const wChan = c.alreadyTransitioned ? undefined : c.absoluteChannel;
                        this.transitionSpec(wChan, undefined);
                    } catch (err) {
                        this.fail(err as Error);
                        return Promise.reject(err);
                    }
                    extReader(c.value);
                    return Promise.resolve(c.callback());
                }
            }
        }

        // 2. Queue all cases under a single transaction
        this.activeTasks--;
        this.checkStatus();

        return new Promise<T>((resolve, reject) => {
            const transaction: SelectTransaction = { resolved: false };
            const cleanupOps: (() => void)[] = [];

            for (const c of resolvedCases) {
                const canonicalKey = this.getCanonicalChannel(c.absoluteChannel.join("."));
                const op: PendingOp = {
                    kind: c.kind,
                    absoluteChannel: c.absoluteChannel,
                    value: c.value,
                    transaction,
                    alreadyTransitioned: c.alreadyTransitioned,
                    resolve: (val) => {
                        this.activeTasks++;
                        resolve(c.callback(val));
                    }
                };

                if (c.kind === "read") {
                    this.pushPendingReader(canonicalKey, op);
                    cleanupOps.push(() => this.removePendingReader(canonicalKey, op));
                } else {
                    this.pushPendingWriter(canonicalKey, op);
                    cleanupOps.push(() => this.removePendingWriter(canonicalKey, op));
                }
            }

            transaction.cleanup = () => {
                cleanupOps.forEach(fn => fn());
            };
        });
    }

    private transitionSpec(writeChannel?: string[], readChannel?: string[]) {
        if (!writeChannel && !readChannel) return;
        let nextSpec = this.spec;
        if (writeChannel && readChannel) {
            let specAfterWrite = transition(nextSpec, { kind: "write", channel: writeChannel });
            let specBoth = specAfterWrite ? transition(specAfterWrite, { kind: "read", channel: readChannel }) : null;
            if (specBoth === null) {
                let specAfterRead = transition(nextSpec, { kind: "read", channel: readChannel });
                specBoth = specAfterRead ? transition(specAfterRead, { kind: "write", channel: writeChannel }) : null;
            }
            if (specBoth === null) {
                throw new Error(`Spec violation: sync between write on [${writeChannel.join(".")}] and read on [${readChannel.join(".")}] not allowed.`);
            }
            this.spec = specBoth;
        } else if (writeChannel) {
            const specAfterWrite = transition(nextSpec, { kind: "write", channel: writeChannel });
            if (specAfterWrite === null) {
                throw new Error(`Spec violation: write on [${writeChannel.join(".")}] not allowed.`);
            }
            this.spec = specAfterWrite;
        } else if (readChannel) {
            const specAfterRead = transition(nextSpec, { kind: "read", channel: readChannel });
            if (specAfterRead === null) {
                throw new Error(`Spec violation: read on [${readChannel.join(".")}] not allowed.`);
            }
            this.spec = specAfterRead;
        }
    }

    private pushPendingReader(key: string, op: PendingOp) {
        if (!this.pendingReaders.has(key)) this.pendingReaders.set(key, []);
        this.pendingReaders.get(key)!.push(op);
    }

    private removePendingReader(key: string, op: PendingOp) {
        const list = this.pendingReaders.get(key);
        if (list) {
            const idx = list.indexOf(op);
            if (idx !== -1) list.splice(idx, 1);
        }
    }

    private popPendingReader(key: string): PendingOp | null {
        const list = this.pendingReaders.get(key);
        if (!list) return null;
        while (list.length > 0) {
            const op = list.shift()!;
            if (!op.transaction || !op.transaction.resolved) {
                if (op.transaction) {
                    op.transaction.resolved = true;
                    op.transaction.cleanup?.();
                }
                return op;
            }
        }
        return null;
    }

    private pushPendingWriter(key: string, op: PendingOp) {
        if (!this.pendingWriters.has(key)) this.pendingWriters.set(key, []);
        this.pendingWriters.get(key)!.push(op);
    }

    private removePendingWriter(key: string, op: PendingOp) {
        const list = this.pendingWriters.get(key);
        if (list) {
            const idx = list.indexOf(op);
            if (idx !== -1) list.splice(idx, 1);
        }
    }

    private popPendingWriter(key: string): PendingOp | null {
        const list = this.pendingWriters.get(key);
        if (!list) return null;
        while (list.length > 0) {
            const op = list.shift()!;
            if (!op.transaction || !op.transaction.resolved) {
                if (op.transaction) {
                    op.transaction.resolved = true;
                    op.transaction.cleanup?.();
                }
                return op;
            }
        }
        return null;
    }

    private popExternalWriter(key: string): ExternalWriter | null {
        const list = this.pendingExternalWriters.get(key);
        if (list && list.length > 0) return list.shift()!;
        return null;
    }

    private pushExternalWriter(key: string, writer: ExternalWriter) {
        if (!this.pendingExternalWriters.has(key)) this.pendingExternalWriters.set(key, []);
        this.pendingExternalWriters.get(key)!.push(writer);
    }

    private popExternalReader(key: string): ExternalReader["resolve"] | null {
        const list = this.pendingExternalReaders.get(key);
        if (list && list.length > 0) return list.shift()!.resolve;
        return null;
    }

    private pushExternalReader(key: string, resolve: ExternalReader["resolve"]) {
        if (!this.pendingExternalReaders.has(key)) this.pendingExternalReaders.set(key, []);
        this.pendingExternalReaders.get(key)!.push({ resolve });
    }
}
