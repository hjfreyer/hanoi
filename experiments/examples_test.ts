import { build, sequence, read, write, choice, loop, concurrent, parseTranscript, checkTranscript, transition, isCompleted, getPossibleTransitions } from "./spec";
import { MachineInstance, StepResult, ConcurrentMachine, TraceMachine, SequenceMachine, WriteConstantMachine, DiscardMachine, LoopMachine, DupMachine } from "./impl";

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

describe("ValueCell example", () => {
    it("can set and copy values step-by-step", () => {
        const machine = new ValueCellMachine(42);

        // Initially copy should return 42
        let res = machine.step({ channel: ["copy"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["copy"], value: null });

        res = machine.step();
        expect(res).toEqual({ kind: "write", channel: ["value"], value: 42 });

        // Set value to 100
        res = machine.step({ channel: ["set"], value: 100 });
        expect(res).toEqual({ kind: "read", channel: ["set"], value: 100 });

        // Copy should now return 100
        res = machine.step({ channel: ["copy"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["copy"], value: null });

        res = machine.step();
        expect(res).toEqual({ kind: "write", channel: ["value"], value: 100 });
    });

    it("verifies a valid execution transcript against ValueCellSpec", () => {
        const transcript = parseTranscript(`
            < copy
            > value
            < set
            < copy
            > value
        `);
        expect(checkTranscript(ValueCellSpec, transcript)).toBe(true);
    });
});

describe("UninitValueCell example", () => {
    it("fails if machine tries to copy before set", () => {
        const machine = new ValueCellMachine();
        // Trying to step copy before setting should not be accepted/should return waiting
        const res = machine.step({ channel: ["copy"], value: null });
        expect(res).toEqual({ kind: "waiting" });
    });

    it("can set first and then copy", () => {
        const machine = new ValueCellMachine();

        // Set value to 25
        let res = machine.step({ channel: ["set"], value: 25 });
        expect(res).toEqual({ kind: "read", channel: ["set"], value: 25 });

        // Now copy should succeed and return 25
        res = machine.step({ channel: ["copy"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["copy"], value: null });

        res = machine.step();
        expect(res).toEqual({ kind: "write", channel: ["value"], value: 25 });
    });

    it("verifies transcripts against UninitValueCellSpec", () => {
        const valid = parseTranscript(`
            < set
            < copy
            > value
        `);
        expect(checkTranscript(UninitValueCellSpec, valid)).toBe(true);

        const invalid = parseTranscript(`
            < copy
            > value
            < set
        `);
        expect(checkTranscript(UninitValueCellSpec, invalid)).toBe(false);
    });
});

// 5. Define the BinaryValue spec (reads x and y, then writes z)
export const BinaryValueSpec = build(sequence(
    concurrent({
        x: build(read([])),
        y: build(read([]))
    }),
    write(["z"])
));

export const AddSpec = BinaryValueSpec;

// 6. Implement the BinaryValueMachine using MachineInstance
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

describe("AddMachine example", () => {
    it("can read x and y in any order and writes sum to z", () => {
        const machine = new AddMachine();
        expect(machine.isCompleted()).toBe(false);
        expect(machine.step()).toEqual({ kind: "waiting" });

        expect(machine.step({ channel: ["x"], value: 15 })).toEqual({ kind: "read", channel: ["x"], value: 15 });
        expect(machine.step()).toEqual({ kind: "waiting" });

        expect(machine.step({ channel: ["y"], value: 25 })).toEqual({ kind: "read", channel: ["y"], value: 25 });
        expect(machine.step()).toEqual({ kind: "write", channel: ["z"], value: 40 });
        expect(machine.isCompleted()).toBe(true);
        expect(machine.step()).toEqual({ kind: "done" });
    });

    it("verifies transcripts against passive AddSpec", () => {
        const valid = parseTranscript(`
            < x
            < y
            > z
        `);
        expect(checkTranscript(AddSpec, valid)).toBe(true);
    });
});

describe("Automated AddMachine Wiring", () => {
    it("wires driver, passive AddMachine, and ValueCells to execute automated sum computation in one step", () => {
        const cellX = new ValueCellMachine(10);
        const cellY = new ValueCellMachine(20);
        const cellZ = new ValueCellMachine();
        const add = new AddMachine();

        // Construct a driver that simply triggers the copies on x and y cells in sequence
        const driver = new SequenceMachine([
            new WriteConstantMachine(["x", "copy"], null),
            new WriteConstantMachine(["y", "copy"], null)
        ]);

        const comp = new ConcurrentMachine({
            system: new ConcurrentMachine({
                x: cellX,
                y: cellY,
                z: cellZ,
                add: add
            }),
            driver: driver
        });

        // 1. Wire the system internally:
        // cellX.value -> add.x
        let systemWired = new TraceMachine(comp, ["system", "x", "value"], ["system", "add", "x"]);
        // cellY.value -> add.y
        systemWired = new TraceMachine(systemWired, ["system", "y", "value"], ["system", "add", "y"]);
        // add.z -> cellZ.set
        systemWired = new TraceMachine(systemWired, ["system", "add", "z"], ["system", "z", "set"]);

        // 2. Wire the driver to the system:
        // driver.x.copy -> system.x.copy
        let wired = new TraceMachine(systemWired, ["driver", "x", "copy"], ["system", "x", "copy"]);
        // driver.y.copy -> system.y.copy
        wired = new TraceMachine(wired, ["driver", "y", "copy"], ["system", "y", "copy"]);

        // Execute the entire pipeline in one single step!
        // It runs silently and terminates since there are no more active writes.
        const res = wired.step();
        expect(res).toEqual({ kind: "done" });
        expect(wired.isCompleted()).toBe(true);

        // Verify cellZ has stored the correct sum of 30!
        expect(cellZ.getValue()).toBe(30);
    });
});

describe("LessThanMachine example", () => {
    it("compares x and y and writes x < y boolean to z", () => {
        // Test case 1: x < y is true
        {
            const machine = new LessThanMachine();
            expect(machine.isCompleted()).toBe(false);
            expect(machine.step()).toEqual({ kind: "waiting" });
            expect(machine.step({ channel: ["x"], value: 10 })).toEqual({ kind: "read", channel: ["x"], value: 10 });
            expect(machine.step({ channel: ["y"], value: 20 })).toEqual({ kind: "read", channel: ["y"], value: 20 });
            expect(machine.step()).toEqual({ kind: "write", channel: ["z"], value: true });
            expect(machine.isCompleted()).toBe(true);
        }

        // Test case 2: x < y is false
        {
            const machine = new LessThanMachine();
            expect(machine.step({ channel: ["x"], value: 50 })).toEqual({ kind: "read", channel: ["x"], value: 50 });
            expect(machine.step({ channel: ["y"], value: 20 })).toEqual({ kind: "read", channel: ["y"], value: 20 });
            expect(machine.step()).toEqual({ kind: "write", channel: ["z"], value: false });
        }
    });
});

export function createFibonacciMachine(): MachineInstance {
    const cellA = new ValueCellMachine(0);
    const cellB = new ValueCellMachine(1);
    const cellTemp = new ValueCellMachine();
    const add = new LoopMachine(() => new AddMachine());
    const dupB = new LoopMachine(() => new DupMachine(["in"], ["out0", "out1", "value"]));

    // Construct the controller dynamically using primitives and LoopMachine
    const controller = new LoopMachine(() => {
        return new SequenceMachine([
            new DiscardMachine(["next"]),
            new WriteConstantMachine(["A", "copy"], null),
            new WriteConstantMachine(["B", "copy"], null),
            new WriteConstantMachine(["Temp", "copy"], null)
        ]);
    });

    const comp = new ConcurrentMachine({
        A: cellA,
        B: cellB,
        Temp: cellTemp,
        add: add,
        dupB: dupB,
        ctrl: controller
    });

    // Wire A.copy
    let wired = new TraceMachine(comp, ["ctrl", "A", "copy"], ["A", "copy"]);

    // Wire A.value -> add.x
    wired = new TraceMachine(wired, ["A", "value"], ["add", "x"]);

    // Wire B.copy
    wired = new TraceMachine(wired, ["ctrl", "B", "copy"], ["B", "copy"]);

    // Wire B.value -> dupB.in
    wired = new TraceMachine(wired, ["B", "value"], ["dupB", "in"]);

    // Wire dupB outputs
    wired = new TraceMachine(wired, ["dupB", "out0"], ["A", "set"]);
    wired = new TraceMachine(wired, ["dupB", "out1"], ["add", "y"]);

    // Wire add.z -> Temp.set
    wired = new TraceMachine(wired, ["add", "z"], ["Temp", "set"]);

    // Wire Temp.copy
    wired = new TraceMachine(wired, ["ctrl", "Temp", "copy"], ["Temp", "copy"]);

    // Wire Temp.value -> B.set
    wired = new TraceMachine(wired, ["Temp", "value"], ["B", "set"]);

    return wired;
}

describe("Fibonacci Machine (pure composition)", () => {
    it("returns sequential Fibonacci numbers on each 'ctrl.next' trigger", () => {
        const fib = createFibonacciMachine();

        // 1st trigger: return 1 (sum of 0 and 1)
        let res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["dupB", "value"], value: 1 });
        // Propagation step: updates cellB with Temp value and resets loop controller
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });

        // 2nd trigger: return 1 (sum of 1 and 1)
        res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["dupB", "value"], value: 1 });
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });

        // 3rd trigger: return 2 (sum of 1 and 1)
        res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["dupB", "value"], value: 2 });
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });

        // 4th trigger: return 3 (sum of 1 and 2)
        res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["dupB", "value"], value: 3 });
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });

        // 5th trigger: return 5 (sum of 2 and 3)
        res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["dupB", "value"], value: 5 });
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });

        // 6th trigger: return 8 (sum of 3 and 5)
        res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["dupB", "value"], value: 8 });
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });

        // 7th trigger: return 13 (sum of 5 and 8)
        res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["dupB", "value"], value: 13 });
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });
    });

    it("verifies transcripts against the resolved Fibonacci spec", () => {
        const fib = createFibonacciMachine();
        const spec = fib.getSpec();

        // The external transcript showing only inputs and outputs
        const valid = parseTranscript(`
            < ctrl.next
            > dupB.value
            < ctrl.next
            > dupB.value
            < ctrl.next
            > dupB.value
        `);
        expect(checkTranscript(spec, valid)).toBe(true);

        // An invalid transcript containing internal channels that should be hidden
        const invalidInternal = parseTranscript(`
            < ctrl.next
            > A.copy
            > dupB.value
        `);
        expect(checkTranscript(spec, invalidInternal)).toBe(false);
    });
});
