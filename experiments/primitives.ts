import { MachineSpec, build, sequence, read, write, choice, loop, concurrent, transition, isCompleted, getPossibleTransitions } from "./spec";
import { MachineInstance, StepResult, channelsEqual } from "./impl";

// 1. Define the ValueCell specs
export const ValueCellSpec = build(loop(build(choice({
    set: build(read(["set"])),
    copy: build(sequence(
        read(["copy"]),
        write(["value"])
    ))
}))));

export const UninitValueCellSpec = build(sequence(
    read(["set"]),
    loop(build(choice({
        set: build(read(["set"])),
        copy: build(sequence(
            read(["copy"]),
            write(["value"])
        ))
    })))
));

// 2. Implement the unified ValueCellMachine using MachineInstance
export class ValueCellMachine implements MachineInstance {
    private spec: any;
    private value: any;
    private state: "uninit" | "ready" | "pending_value";

    constructor(initialValue?: any) {
        if (initialValue !== undefined) {
            this.value = initialValue;
            this.spec = ValueCellSpec;
            this.state = "ready";
        } else {
            this.spec = UninitValueCellSpec;
            this.state = "uninit";
        }
    }

    getValue() {
        return this.value;
    }

    getSpec() {
        return this.spec;
    }

    isCompleted() {
        return isCompleted(this.spec);
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.state === "uninit") {
            if (!action || action.channel[0] !== "set") {
                return { kind: "waiting" };
            }
            const next = transition(this.spec, { kind: "read", channel: ["set"] });
            if (!next) throw new Error("Invalid transition");
            this.spec = next;
            this.value = action.value;
            this.state = "ready";
            return { kind: "read", channel: ["set"], value: action.value };
        }

        if (this.state === "ready") {
            if (!action) {
                return { kind: "waiting" };
            }
            if (action.channel[0] === "set") {
                const next = transition(this.spec, { kind: "read", channel: ["set"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.value = action.value;
                return { kind: "read", channel: ["set"], value: action.value };
            }
            if (action.channel[0] === "copy") {
                const next = transition(this.spec, { kind: "read", channel: ["copy"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.state = "pending_value";
                return { kind: "read", channel: ["copy"], value: action.value };
            }
            throw new Error(`Invalid action channel: ${action.channel}`);
        } else {
            const next = transition(this.spec, { kind: "write", channel: ["value"] });
            if (!next) throw new Error("Invalid transition");
            this.spec = next;
            this.state = "ready";
            return { kind: "write", channel: ["value"], value: this.value };
        }
    }
}

// 3. Define the BinaryValue spec (reads x and y, then writes z)
export const BinaryValueSpec = build(sequence(
    concurrent({
        x: build(read([])),
        y: build(read([]))
    }),
    write(["z"])
));

export const AddSpec = BinaryValueSpec;

// 4. Implement the BinaryValueMachine using MachineInstance
export class BinaryValueMachine implements MachineInstance {
    private spec = BinaryValueSpec;
    private xVal?: any;
    private yVal?: any;
    private state: "waiting" | "ready_z" | "done" = "waiting";

    constructor(private op: (x: any, y: any) => any) {}

    getSpec() {
        return this.spec;
    }

    isCompleted() {
        return isCompleted(this.spec);
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.state === "waiting") {
            if (!action) {
                return { kind: "waiting" };
            }
            if (action.channel[0] === "x") {
                const next = transition(this.spec, { kind: "read", channel: ["x"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.xVal = action.value;
                this.checkReady();
                return { kind: "read", channel: ["x"], value: action.value };
            }
            if (action.channel[0] === "y") {
                const next = transition(this.spec, { kind: "read", channel: ["y"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.yVal = action.value;
                this.checkReady();
                return { kind: "read", channel: ["y"], value: action.value };
            }
            throw new Error(`Invalid channel: ${action.channel}`);
        } else if (this.state === "ready_z") {
            const next = transition(this.spec, { kind: "write", channel: ["z"] });
            if (!next) throw new Error("Invalid transition");
            this.spec = next;
            this.state = "done";
            return { kind: "write", channel: ["z"], value: this.op(this.xVal, this.yVal) };
        }
        return { kind: "done" };
    }

    private checkReady() {
        if (this.xVal !== undefined && this.yVal !== undefined) {
            this.state = "ready_z";
        }
    }
}

export class AddMachine extends BinaryValueMachine {
    constructor() {
        super((x, y) => x + y);
    }
}

export class LessThanMachine extends BinaryValueMachine {
    constructor() {
        super((x, y) => x < y);
    }
}

// 5. Implement AssignCellMachine
export class AssignCellMachine implements MachineInstance {
    private spec: MachineSpec;
    private state: "copying" | "reading" | "writing" | "done" = "copying";
    private val: any;
    private copyChan: string[];
    private readChan: string[];
    private setChan: string[];

    constructor(src: string[], dest: string[]) {
        this.copyChan = [...src, "copy"];
        this.readChan = [...src, "value"];
        this.setChan = [...dest, "set"];
        this.spec = build(sequence(
            write(this.copyChan),
            read(this.readChan),
            write(this.setChan)
        ));
    }

    getSpec() {
        return this.spec;
    }

    isCompleted() {
        return this.state === "done";
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.state === "copying") {
            const possible = getPossibleTransitions(this.spec);
            const writeTrans = possible.find(t => t.kind === "write");
            if (writeTrans) {
                const nextSpec = transition(this.spec, writeTrans);
                if (!nextSpec) throw new Error("Invalid transition on copy");
                this.spec = nextSpec;
                this.state = "reading";
                return { kind: "write", channel: writeTrans.channel, value: null };
            }
            this.state = "reading";
        }

        if (this.state === "reading") {
            if (!action || !channelsEqual(action.channel, this.readChan)) {
                return { kind: "waiting" };
            }
            const nextSpec = transition(this.spec, { kind: "read", channel: this.readChan });
            if (!nextSpec) throw new Error("Invalid transition on read");
            this.spec = nextSpec;
            this.val = action.value;
            this.state = "writing";
            return { kind: "read", channel: this.readChan, value: action.value };
        }

        if (this.state === "writing") {
            const possible = getPossibleTransitions(this.spec);
            const writeTrans = possible.find(t => t.kind === "write");
            if (writeTrans) {
                const nextSpec = transition(this.spec, writeTrans);
                if (!nextSpec) throw new Error("Invalid transition on set");
                this.spec = nextSpec;
                this.state = "done";
                return { kind: "write", channel: writeTrans.channel, value: this.val };
            }
            this.state = "done";
        }

        return { kind: "done" };
    }
}

// 6. Implement BinaryCellMachine and AddCellMachine
export class BinaryCellMachine implements MachineInstance {
    private spec: MachineSpec;
    private state: "reading" | "writing" | "done" = "reading";
    private xVal: any = 0;
    private yVal: any = 0;
    private xKey: string;
    private yKey: string;
    private remainingReads = new Set<string>();

    constructor(srcX: string[], srcY: string[], destZ: string[], private op: (x: any, y: any) => any) {
        this.xKey = srcX[srcX.length - 1];
        this.yKey = srcY[srcY.length - 1];
        this.remainingReads.add(this.xKey);
        this.remainingReads.add(this.yKey);

        this.spec = build(sequence(
            concurrent({
                [this.xKey]: build(sequence(write(["copy"]), read(["value"]))),
                [this.yKey]: build(sequence(write(["copy"]), read(["value"])))
            }),
            write([...destZ, "set"])
        ));
    }

    getSpec() {
        return this.spec;
    }

    isCompleted() {
        return this.state === "done";
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.state === "reading") {
            if (action) {
                const key = action.channel[0];
                if (this.remainingReads.has(key)) {
                    const nextSpec = transition(this.spec, { kind: "read", channel: action.channel });
                    if (nextSpec) {
                        this.spec = nextSpec;
                        if (key === this.xKey) this.xVal = action.value;
                        else if (key === this.yKey) this.yVal = action.value;

                        this.remainingReads.delete(key);
                        if (this.remainingReads.size === 0) {
                            this.state = "writing";
                        }
                        return { kind: "read", channel: action.channel, value: action.value };
                    }
                }
            }

            const possible = getPossibleTransitions(this.spec);
            const writeTrans = possible.find(t => t.kind === "write");
            if (writeTrans) {
                const nextSpec = transition(this.spec, writeTrans);
                if (!nextSpec) throw new Error("Invalid transition on write copy");
                this.spec = nextSpec;
                return { kind: "write", channel: writeTrans.channel, value: null };
            }

            return { kind: "waiting" };
        }

        if (this.state === "writing") {
            const possible = getPossibleTransitions(this.spec);
            const writeTrans = possible.find(t => t.kind === "write");
            if (writeTrans) {
                const nextSpec = transition(this.spec, writeTrans);
                if (!nextSpec) throw new Error("Invalid transition on z write");
                this.spec = nextSpec;
                this.state = "done";
                return { kind: "write", channel: writeTrans.channel, value: this.op(this.xVal, this.yVal) };
            }
            this.state = "done";
        }

        return { kind: "done" };
    }
}

export class AddCellMachine extends BinaryCellMachine {
    constructor(srcX: string[], srcY: string[], destZ: string[]) {
        super(srcX, srcY, destZ, (x, y) => x + y);
    }
}
