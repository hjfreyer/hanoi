import { MachineSpec, build, sequence, read, write, choice, loop, concurrent, transition, isCompleted, getPossibleTransitions, indexed } from "./spec";
import { MachineInstance, StepResult, channelsEqual } from "./impl";

// 1. Define the ValueCell specs
export const ValueCellSpec = build(indexed(build(choice({
    set: build(read(["set"])),
    copy: build(sequence(
        read(["copy"]),
        write(["value"])
    ))
}))));

export const UninitValueCellSpec = build(sequence(
    indexed(build(read(["set"]))),
    indexed(build(choice({
        set: build(read(["set"])),
        copy: build(sequence(
            read(["copy"]),
            write(["value"])
        ))
    })))
));

// 2. Implement the unified ValueCellMachine using MachineInstance
export class ValueCellMachine implements MachineInstance {
    private spec: MachineSpec;
    private value: any;

    constructor(initialValue?: any) {
        if (initialValue !== undefined) {
            this.value = initialValue;
            this.spec = ValueCellSpec;
        } else {
            this.spec = UninitValueCellSpec;
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
        if (action) {
            const isWrite = action.channel[action.channel.length - 1] === "value";
            const transcriptKind = isWrite ? "write" : "read";
            
            const nextSpec = transition(this.spec, { kind: transcriptKind, channel: action.channel });
            if (!nextSpec) {
                return { kind: "waiting" };
            }
            
            this.spec = nextSpec;
            if (action.channel[action.channel.length - 1] === "set") {
                this.value = action.value;
            }
            return { kind: transcriptKind, channel: action.channel, value: action.value };
        }

        const possible = getPossibleTransitions(this.spec);
        const writeTransitions = possible.filter(t => t.kind === "write");
        
        
        if (writeTransitions.length > 0) {
            const t = writeTransitions[0];
            const nextSpec = transition(this.spec, t);
            if (nextSpec) {
                this.spec = nextSpec;
                return { kind: "write", channel: t.channel, value: this.value };
            }
        }

        return { kind: "waiting" };
    }
}

// 3. Define the BinaryValue spec (reads in0 and in1, then writes out0)
export const BinaryValueSpec = build(sequence(
    concurrent({
        in0: build(read([])),
        in1: build(read([]))
    }),
    write(["out0"])
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
            if (action.channel[0] === "in0") {
                const next = transition(this.spec, { kind: "read", channel: ["in0"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.xVal = action.value;
                this.checkReady();
                return { kind: "read", channel: ["in0"], value: action.value };
            }
            if (action.channel[0] === "in1") {
                const next = transition(this.spec, { kind: "read", channel: ["in1"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.yVal = action.value;
                this.checkReady();
                return { kind: "read", channel: ["in1"], value: action.value };
            }
            throw new Error(`Invalid channel: ${action.channel}`);
        } else if (this.state === "ready_z") {
            const next = transition(this.spec, { kind: "write", channel: ["out0"] });
            if (!next) throw new Error("Invalid transition");
            this.spec = next;
            this.state = "done";
            return { kind: "write", channel: ["out0"], value: this.op(this.xVal, this.yVal) };
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

export const BinaryPredicateSpec = build(sequence(
    concurrent({
        in0: build(read([])),
        in1: build(read([]))
    }),
    choice({
        true: build(write(["out0", "true"])),
        false: build(write(["out0", "false"]))
    })
));

export const LessThanSpec = BinaryPredicateSpec;

export class BinaryPredicateMachine implements MachineInstance {
    private spec = BinaryPredicateSpec;
    private xVal?: any;
    private yVal?: any;
    private state: "waiting" | "ready_output" | "done" = "waiting";

    constructor(private pred: (x: any, y: any) => boolean) {}

    getSpec() {
        return this.spec;
    }

    isCompleted() {
        return this.state === "done";
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.state === "waiting") {
            if (!action) {
                return { kind: "waiting" };
            }
            if (action.channel[0] === "in0") {
                const next = transition(this.spec, { kind: "read", channel: ["in0"] });
                if (!next) throw new Error("Invalid transition on in0");
                this.spec = next;
                this.xVal = action.value;
                this.checkReady();
                return { kind: "read", channel: ["in0"], value: action.value };
            }
            if (action.channel[0] === "in1") {
                const next = transition(this.spec, { kind: "read", channel: ["in1"] });
                if (!next) throw new Error("Invalid transition on in1");
                this.spec = next;
                this.yVal = action.value;
                this.checkReady();
                return { kind: "read", channel: ["in1"], value: action.value };
            }
            throw new Error(`Invalid channel: ${action.channel}`);
        } else if (this.state === "ready_output") {
            const outChan = this.pred(this.xVal, this.yVal) ? ["out0", "true"] : ["out0", "false"];
            const next = transition(this.spec, { kind: "write", channel: outChan });
            if (!next) throw new Error(`Invalid transition on write ${outChan.join(".")}`);
            this.spec = next;
            this.state = "done";
            return { kind: "write", channel: outChan, value: null };
        }
        return { kind: "done" };
    }

    private checkReady() {
        if (this.xVal !== undefined && this.yVal !== undefined) {
            this.state = "ready_output";
        }
    }
}

export class LessThanMachine extends BinaryPredicateMachine {
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

    constructor() {
        this.copyChan = ["in0", "copy"];
        this.readChan = ["in0", "value"];
        this.setChan = ["out0", "set"];
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
    private remainingReads = new Set<string>();

    constructor(private op: (x: any, y: any) => any) {
        this.remainingReads.add("in0");
        this.remainingReads.add("in1");

        this.spec = build(sequence(
            concurrent({
                in0: build(sequence(write(["copy"]), read(["value"]))),
                in1: build(sequence(write(["copy"]), read(["value"])))
            }),
            write(["out0", "set"])
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
                        if (key === "in0") this.xVal = action.value;
                        else if (key === "in1") this.yVal = action.value;

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
    constructor() {
        super((x, y) => x + y);
    }
}

export class BinaryPredicateCellMachine implements MachineInstance {
    private spec: MachineSpec;
    private state: "reading" | "writing" | "done" = "reading";
    private xVal: any = 0;
    private yVal: any = 0;
    private remainingReads = new Set<string>();

    constructor(private pred: (x: any, y: any) => boolean) {
        this.remainingReads.add("in0");
        this.remainingReads.add("in1");

        this.spec = build(sequence(
            concurrent({
                in0: build(sequence(write(["copy"]), read(["value"]))),
                in1: build(sequence(write(["copy"]), read(["value"])))
            }),
            choice({
                true: build(write(["out0", "true"])),
                false: build(write(["out0", "false"]))
            })
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
                        if (key === "in0") this.xVal = action.value;
                        else if (key === "in1") this.yVal = action.value;

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
            const outChan = this.pred(this.xVal, this.yVal) ? ["out0", "true"] : ["out0", "false"];
            const next = transition(this.spec, { kind: "write", channel: outChan });
            if (!next) throw new Error(`Invalid transition on write ${outChan.join(".")}`);
            this.spec = next;
            this.state = "done";
            return { kind: "write", channel: outChan, value: null };
        }

        return { kind: "done" };
    }
}

export class LessThanCellMachine extends BinaryPredicateCellMachine {
    constructor() {
        super((x, y) => x < y);
    }
}

export const TestSpec = build(sequence(
    read(["input"]),
    choice({
        true: build(write(["out0", "true"])),
        false: build(write(["out0", "false"]))
    })
));

export class TestMachine implements MachineInstance {
    private spec: MachineSpec = TestSpec;
    private inputVal = false;
    private state: "reading" | "writing" | "done" = "reading";

    getSpec() {
        return this.spec;
    }

    isCompleted() {
        return this.state === "done";
    }

    step(action?: { channel: string[]; value?: any }): StepResult {
        if (this.state === "reading") {
            if (!action || !channelsEqual(action.channel, ["input"])) {
                return { kind: "waiting" };
            }
            const next = transition(this.spec, { kind: "read", channel: ["input"] });
            if (!next) throw new Error("Invalid transition on read input");
            this.spec = next;
            this.inputVal = !!action.value;
            this.state = "writing";
            return { kind: "read", channel: ["input"], value: action.value };
        }

        if (this.state === "writing") {
            const outChan = this.inputVal ? ["out0", "true"] : ["out0", "false"];
            const next = transition(this.spec, { kind: "write", channel: outChan });
            if (!next) throw new Error(`Invalid transition on write ${outChan.join(".")}`);
            this.spec = next;
            this.state = "done";
            return { kind: "write", channel: outChan, value: null };
        }

        return { kind: "done" };
    }
}
