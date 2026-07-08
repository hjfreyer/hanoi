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

function getSuffix(channel: string[], prefix: string[]): string[] | null {
    if (channel.length < prefix.length) return null;
    for (let i = 0; i < prefix.length; i++) {
        if (channel[i] !== prefix[i]) return null;
    }
    return channel.slice(prefix.length);
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
                const suffixA = getSuffix(current.channel, this.pathA);
                if (suffixA !== null) {
                    this.inner.step({ channel: [...this.pathB, ...suffixA], value: current.value });
                    current = this.inner.step();
                    continue;
                }
                const suffixB = getSuffix(current.channel, this.pathB);
                if (suffixB !== null) {
                    this.inner.step({ channel: [...this.pathA, ...suffixB], value: current.value });
                    current = this.inner.step();
                    continue;
                }
            }
            if (current.kind === "read") {
                if (getSuffix(current.channel, this.pathA) !== null || getSuffix(current.channel, this.pathB) !== null) {
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

export class ChoiceMachine implements MachineInstance {
    private machines: Record<string, MachineInstance>;
    private selected?: string;

    constructor(machines: Record<string, MachineInstance>) {
        this.machines = machines;
    }

    getSpec(): MachineSpec {
        const subSpecs: Record<string, MachineSpec> = {};
        for (const [key, sub] of Object.entries(this.machines)) {
            subSpecs[key] = sub.getSpec();
        }
        return {
            kind: "choice",
            choices: subSpecs,
            then: { kind: "done" },
            selected: this.selected,
            current: this.selected ? this.machines[this.selected].getSpec() : undefined
        };
    }

    isCompleted(): boolean {
        if (this.selected === undefined) {
            return false;
        }
        return this.machines[this.selected].isCompleted();
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.selected !== undefined) {
            return this.machines[this.selected].step(action);
        }

        if (action) {
            // Find which sub-machine can accept this read action
            for (const [key, sub] of Object.entries(this.machines)) {
                const next = transition(sub.getSpec(), { kind: "read", channel: action.channel });
                if (next !== null) {
                    this.selected = key;
                    return sub.step(action);
                }
            }
            return { kind: "waiting" };
        }

        // Check if any sub-machine wants to write
        for (const [key, sub] of Object.entries(this.machines)) {
            const res = sub.step();
            if (res.kind === "write") {
                this.selected = key;
                return res;
            }
        }

        return { kind: "waiting" };
    }
}

export class PrefixMachine implements MachineInstance {
    private inner: MachineInstance;
    private prefixPath: string[];

    constructor(prefixPath: string[], inner: MachineInstance) {
        this.inner = inner;
        this.prefixPath = prefixPath;
    }

    getSpec(): MachineSpec {
        return {
            kind: "prefix",
            prefix: this.prefixPath,
            inner: this.inner.getSpec(),
            then: { kind: "done" }
        };
    }

    isCompleted(): boolean {
        return this.inner.isCompleted();
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (action) {
            const suffix = getSuffix(action.channel, this.prefixPath);
            if (suffix === null) {
                return { kind: "waiting" };
            }
            const res = this.inner.step({ channel: suffix, value: action.value });
            return this.wrapResult(res);
        }

        const res = this.inner.step();
        return this.wrapResult(res);
    }

    private wrapResult(res: StepResult): StepResult {
        if (res.kind === "read" || res.kind === "write") {
            return {
                ...res,
                channel: [...this.prefixPath, ...res.channel]
            };
        }
        return res;
    }
}

export class RenameMachine implements MachineInstance {
    private inner: MachineInstance;
    private mapping: Array<[string[], string[]]>;

    constructor(inner: MachineInstance, mapping: Array<[string[], string[]]>) {
        this.inner = inner;
        this.mapping = mapping;
    }

    getSpec(): MachineSpec {
        return {
            kind: "rename",
            mapping: this.mapping,
            inner: this.inner.getSpec(),
            then: { kind: "done" }
        };
    }

    isCompleted(): boolean {
        return this.inner.isCompleted();
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (action) {
            const mappedChan = this.translateOuterToInner(action.channel);
            if (mappedChan === null) {
                return { kind: "waiting" };
            }
            const res = this.inner.step({ channel: mappedChan, value: action.value });
            return this.wrapResult(res);
        }

        const res = this.inner.step();
        return this.wrapResult(res);
    }

    private translateOuterToInner(chan: string[]): string[] | null {
        for (const [from, to] of this.mapping) {
            if (getSuffix(chan, from) !== null && !channelsEqual(from, to)) {
                return null;
            }
        }
        for (const [from, to] of this.mapping) {
            const suffix = getSuffix(chan, to);
            if (suffix !== null) {
                return [...from, ...suffix];
            }
        }
        return chan;
    }

    private wrapResult(res: StepResult): StepResult {
        if (res.kind === "read" || res.kind === "write") {
            return {
                ...res,
                channel: this.translateInnerToOuter(res.channel)
            };
        }
        return res;
    }

    private translateInnerToOuter(chan: string[]): string[] {
        for (const [from, to] of this.mapping) {
            const suffix = getSuffix(chan, from);
            if (suffix !== null) {
                return [...to, ...suffix];
            }
        }
        return chan;
    }
}

export class IndexedMachine implements MachineInstance {
    private factory: () => MachineInstance;
    private active: Record<string, MachineInstance> = {};
    private templateSpec: MachineSpec;

    constructor(factory: () => MachineInstance, active: Record<string, MachineInstance> = {}) {
        this.factory = factory;
        this.active = active;
        const dummy = factory();
        this.templateSpec = dummy.getSpec();
    }

    getSpec(): MachineSpec {
        const activeSpecs: Record<string, MachineSpec> = {};
        for (const [key, sub] of Object.entries(this.active)) {
            activeSpecs[key] = sub.getSpec();
        }
        return {
            kind: "indexed",
            inner: this.templateSpec,
            active: activeSpecs,
            then: { kind: "done" }
        };
    }

    isCompleted(): boolean {
        return Object.values(this.active).every(sub => sub.isCompleted());
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (action && action.channel.length > 0) {
            const index = action.channel[0];
            const suffix = action.channel.slice(1);
            
            if (!this.active[index]) {
                this.active[index] = this.factory();
            }
            
            const sub = this.active[index];
            const res = sub.step({ channel: suffix, value: action.value });
            
            if (sub.isCompleted()) {
                delete this.active[index];
            }
            
            if (res.kind === "read" || res.kind === "write") {
                return {
                    ...res,
                    channel: [index, ...res.channel]
                };
            }
            return res;
        }

        for (const [key, sub] of Object.entries(this.active)) {
            const res = sub.step();
            if (res.kind === "write") {
                if (sub.isCompleted()) {
                    delete this.active[key];
                }
                return {
                    kind: "write",
                    channel: [key, ...res.channel],
                    value: res.value
                };
            }
        }

        return { kind: "waiting" };
    }
}



