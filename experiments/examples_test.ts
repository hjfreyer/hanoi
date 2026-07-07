// NOTE: All examples in this file must only use primitives (from primitives.ts) and combinators (from impl.ts), rather than implementing custom JS functionality directly.

import { MachineInstance, ConcurrentMachine, TraceMachine, SequenceMachine, DiscardMachine, LoopMachine } from "./impl";
import {
    ValueCellMachine,
    AssignCellMachine,
    AddCellMachine
} from "./primitives";

export function createFibonacciMachine2(): MachineInstance {
    const cellA = new ValueCellMachine(0);
    const cellB = new ValueCellMachine(1);
    const cellC = new ValueCellMachine(1);

    const controller = new LoopMachine(() => {
        return new SequenceMachine([
            new DiscardMachine(["next"]),
            new AssignCellMachine(["B"], ["out"]),
            new AddCellMachine(["A"], ["B"], ["C"]),
            new AssignCellMachine(["B"], ["A"]),
            new AssignCellMachine(["C"], ["B"])
        ]);
    });

    const comp = new ConcurrentMachine({
        A: cellA,
        B: cellB,
        C: cellC,
        ctrl: controller
    });

    // Wire cells A, B, and C to controller using prefix wiring
    let wired = new TraceMachine(comp, ["ctrl", "A"], ["A"]);
    wired = new TraceMachine(wired, ["ctrl", "B"], ["B"]);
    wired = new TraceMachine(wired, ["ctrl", "C"], ["C"]);

    return wired;
}

describe("Fibonacci Machine 2 (sequential assignment)", () => {
    it("returns sequential Fibonacci numbers on each 'ctrl.next' trigger", () => {
        const fib = createFibonacciMachine2();

        // 1st trigger: return 1 (initial B)
        let res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["ctrl", "out", "set"], value: 1 });
        
        // Single propagation tick: runs add, shift1, shift2, and resets loop
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });

        // 2nd trigger: return 1 (value of B after 1st update)
        res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["ctrl", "out", "set"], value: 1 });
        
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });

        // 3rd trigger: return 2
        res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["ctrl", "out", "set"], value: 2 });
        
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });

        // 4th trigger: return 3
        res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["ctrl", "out", "set"], value: 3 });
        
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });

        // 5th trigger: return 5
        res = fib.step({ channel: ["ctrl", "next"], value: null });
        expect(res).toEqual({ kind: "read", channel: ["ctrl", "next"], value: null });
        res = fib.step();
        expect(res).toEqual({ kind: "write", channel: ["ctrl", "out", "set"], value: 5 });
        
        res = fib.step();
        expect(res).toEqual({ kind: "waiting" });
    });
});
