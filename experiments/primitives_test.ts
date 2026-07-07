import { parseTranscript, checkTranscript } from "./spec";
import { ConcurrentMachine, TraceMachine, SequenceMachine, WriteConstantMachine } from "./impl";
import {
    ValueCellSpec,
    UninitValueCellSpec,
    ValueCellMachine,
    AddSpec,
    AddMachine,
    LessThanMachine,
    AddCellMachine
} from "./primitives";

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
        // driver.x.copy -> system.x.copy, driver.y.copy -> system.y.copy
        let wired = new TraceMachine(systemWired, ["driver"], ["system"]);

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

describe("AddCellMachine", () => {
    it("requests copy from cell X and cell Y, and writes the sum to cell Z", () => {
        const cellX = new ValueCellMachine(10);
        const cellY = new ValueCellMachine(20);
        const cellZ = new ValueCellMachine();
        const add = new AddCellMachine(["x"], ["y"], ["z"]);

        const comp = new ConcurrentMachine({
            x: cellX,
            y: cellY,
            z: cellZ,
            add: add
        });

        let wired = new TraceMachine(comp, ["add", "x"], ["x"]);
        wired = new TraceMachine(wired, ["add", "y"], ["y"]);
        wired = new TraceMachine(wired, ["add", "z"], ["z"]);

        const res = wired.step();
        expect(res).toEqual({ kind: "done" });

        expect(cellZ.getValue()).toBe(30);
    });
});
