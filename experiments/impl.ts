import { MachineSpec, transition, isCompleted, build, read, write, loop, concurrent, sequence, getPossibleTransitions } from "./spec";

export type StepResult =
    | { kind: "write"; channel: string[]; value: any }
    | { kind: "read"; channel: string[]; value: any }
    | { kind: "waiting" }
    | { kind: "done" };

export interface MachineInstance {
    getSpec(): MachineSpec;
    isCompleted(): boolean;
    step(action?: { channel: string[]; value?: any }): StepResult;
}

export function concatSpecs(a: MachineSpec, b: MachineSpec): MachineSpec {
    if (a.kind === "done") {
        return b;
    }
    return {
        ...a,
        then: concatSpecs(a.then, b)
    } as MachineSpec;
}

export class SequenceMachine implements MachineInstance {
    private machines: MachineInstance[];
    private currentIndex = 0;

    constructor(machines: MachineInstance[]) {
        this.machines = machines;
    }

    getSpec(): MachineSpec {
        let spec: MachineSpec = { kind: "done" };
        for (let i = this.machines.length - 1; i >= this.currentIndex; i--) {
            spec = concatSpecs(this.machines[i].getSpec(), spec);
        }
        return spec;
    }

    isCompleted(): boolean {
        return this.currentIndex >= this.machines.length || this.machines.slice(this.currentIndex).every(m => m.isCompleted());
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.currentIndex >= this.machines.length) {
            return { kind: "done" };
        }

        const active = this.machines[this.currentIndex];
        const res = active.step(action);
        if (res.kind === "done") {
            this.currentIndex++;
            return this.step(action);
        }
        return res;
    }
}

export class ConcurrentMachine implements MachineInstance {
    private machines: Record<string, MachineInstance>;

    constructor(machines: Record<string, MachineInstance>) {
        this.machines = machines;
    }

    getSpec(): MachineSpec {
        const subSpecs: Record<string, MachineSpec> = {};
        for (const [key, sub] of Object.entries(this.machines)) {
            subSpecs[key] = sub.getSpec();
        }
        return {
            kind: "concurrent",
            machines: subSpecs,
            then: { kind: "done" }
        };
    }

    isCompleted(): boolean {
        return Object.values(this.machines).every(sub => sub.isCompleted());
    }
    step(action?: { channel: string[]; value?: any }): StepResult {
        if (action && action.channel.length > 0) {
            const key = action.channel[0];
            const sub = this.machines[key];
            if (!sub) {
                return { kind: "waiting" };
            }
            const res = sub.step({ channel: action.channel.slice(1), value: action.value });
            if (res.kind === "read" || res.kind === "write") {
                return {
                    ...res,
                    channel: [key, ...res.channel]
                };
            }
            return res;
        }

        // Try to let sub-machines perform writes
        for (const [key, sub] of Object.entries(this.machines)) {
            if (sub.isCompleted()) continue;
            const res = sub.step();
            if (res.kind === "write") {
                return {
                    kind: "write",
                    channel: [key, ...res.channel],
                    value: res.value
                };
            }
        }

        if (this.isCompleted()) {
            return { kind: "done" };
        }

        return { kind: "waiting" };
    }
}

export function channelsEqual(a: string[], b: string[]): boolean {
    if (a.length !== b.length) return false;
    return a.every((val, index) => val === b[index]);
}

export class TraceMachine implements MachineInstance {
    private inner: MachineInstance;
    private pathA: string[];
    private pathB: string[];

    constructor(inner: MachineInstance, pathA: string[], pathB: string[]) {
        this.inner = inner;
        this.pathA = pathA;
        this.pathB = pathB;
    }

    getSpec(): MachineSpec {
        return {
            kind: "trace",
            inner: this.inner.getSpec(),
            pathA: this.pathA,
            pathB: this.pathB,
            then: { kind: "done" }
        };
    }

    isCompleted(): boolean {
        return this.inner.isCompleted();
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (action) {
            const res = this.inner.step(action);
            return this.processInternal(res);
        }

        const res = this.inner.step();
        return this.processInternal(res);
    }

    private processInternal(res: StepResult): StepResult {
        let current = res;
        while (true) {
            if (current.kind === "write") {
                if (channelsEqual(current.channel, this.pathA)) {
                    this.inner.step({ channel: this.pathB, value: current.value });
                    current = this.inner.step();
                    continue;
                }
                if (channelsEqual(current.channel, this.pathB)) {
                    this.inner.step({ channel: this.pathA, value: current.value });
                    current = this.inner.step();
                    continue;
                }
            }
            if (current.kind === "read") {
                if (channelsEqual(current.channel, this.pathA) || channelsEqual(current.channel, this.pathB)) {
                    current = this.inner.step();
                    continue;
                }
            }
            break;
        }
        return current;
    }
}

export class WriteConstantMachine implements MachineInstance {
    private spec: MachineSpec;
    private done = false;

    constructor(private channel: string[], private value: any) {
        this.spec = build(write(channel));
    }

    getSpec(): MachineSpec {
        return this.spec;
    }

    isCompleted(): boolean {
        return this.done;
    }

    step(): StepResult {
        if (this.done) return { kind: "done" };
        this.spec = { kind: "done" };
        this.done = true;
        return { kind: "write", channel: this.channel, value: this.value };
    }
}

export class DiscardMachine implements MachineInstance {
    private spec: MachineSpec;
    private done = false;
    private val: any = undefined;

    constructor(private channel: string[]) {
        this.spec = build(read(channel));
    }

    getSpec(): MachineSpec {
        return this.spec;
    }

    isCompleted(): boolean {
        return this.done;
    }

    getValue(): any {
        return this.val;
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.done) return { kind: "done" };
        if (!action || !channelsEqual(action.channel, this.channel)) {
            return { kind: "waiting" };
        }
        this.spec = { kind: "done" };
        this.done = true;
        this.val = action.value;
        return { kind: "read", channel: this.channel, value: action.value };
    }
}

export class LoopMachine implements MachineInstance {
    private current: MachineInstance;

    constructor(private factory: () => MachineInstance) {
        this.current = this.factory();
    }

    getSpec(): MachineSpec {
        return build(loop(this.current.getSpec()));
    }

    isCompleted(): boolean {
        return false;
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.current.isCompleted()) {
            this.current = this.factory();
        }
        return this.current.step(action);
    }
}

export class DupMachine implements MachineInstance {
    private spec: MachineSpec;
    private state: "waiting" | "ready" | "done" = "waiting";
    private val: any = undefined;

    constructor(private inChannel: string[], private outKeys: string[]) {
        const concurrentWrites = concurrent(
            Object.fromEntries(outKeys.map(key => [key, build(write([]))]))
        );
        this.spec = build(sequence(read(inChannel), concurrentWrites));
    }

    getSpec() {
        return this.spec;
    }

    isCompleted() {
        return this.state === "done";
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.state === "waiting") {
            if (!action || !channelsEqual(action.channel, this.inChannel)) {
                return { kind: "waiting" };
            }
            const next = transition(this.spec, { kind: "read", channel: this.inChannel });
            if (!next) throw new Error("Invalid transition");
            this.spec = next;
            this.val = action.value;
            this.state = "ready";
            return { kind: "read", channel: this.inChannel, value: action.value };
        }

        if (this.state === "ready") {
            const possible = getPossibleTransitions(this.spec);
            const writeTrans = possible.find(t => t.kind === "write");
            if (writeTrans) {
                const next = transition(this.spec, writeTrans);
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                if (isCompleted(this.spec)) {
                    this.state = "done";
                }
                return { kind: "write", channel: writeTrans.channel, value: this.val };
            }
            this.state = "done";
        }

        return { kind: "done" };
    }
}
