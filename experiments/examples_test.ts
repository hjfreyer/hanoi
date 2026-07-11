// NOTE: All examples in this file must only use primitives (from primitives.ts) and combinators (from impl.ts), rather than implementing custom JS functionality directly.

import {
  MachineInstance,
  ConcurrentMachine,
  TraceMachine,
  SequenceMachine,
  DiscardMachine,
  LoopMachine,
  RenameMachine,
  ChoiceMachine,
  findStateForMachine,
} from "./impl";
import {
  ValueCellMachine,
  AssignCellMachine,
  AddCellMachine,
  LessThanCellMachine,
} from "./primitives";

class Runner {
  private state: any;
  constructor(private machine: any) {
    this.state = machine.createState();
  }
  isCompleted(): boolean {
    return this.machine.isCompleted(this.state);
  }
  getSpec(): any {
    return this.machine.getSpec(this.state);
  }
  step(action?: { channel: string[]; value?: any }): any {
    const { result, state } = this.machine.step(this.state, action);
    this.state = state;
    return result;
  }
  getState(): any {
    return this.state;
  }
}

function makeUnindexedCell(cell: ValueCellMachine): RenameMachine {
  return new RenameMachine(cell, [
    [["p0", "copy"], ["copy"]],
    [["p0", "value"], ["value"]],
    [["p0", "set"], ["set"]],
  ]);
}

export function createFibonacciMachine2(): MachineInstance {
  const cellA = new ValueCellMachine(0);
  const cellB = new ValueCellMachine(1);
  const cellC = new ValueCellMachine(1);

  const controller = new LoopMachine(() => {
    return new SequenceMachine([
      new DiscardMachine(["next"]),
      new RenameMachine(new AssignCellMachine(), [
        [["in0"], ["B"]],
        [["out0"], ["out0"]],
      ]),
      new RenameMachine(new AddCellMachine(), [
        [["in0"], ["A"]],
        [["in1"], ["B"]],
        [["out0"], ["C"]],
      ]),
      new RenameMachine(new AssignCellMachine(), [
        [["in0"], ["B"]],
        [["out0"], ["A"]],
      ]),
      new RenameMachine(new AssignCellMachine(), [
        [["in0"], ["C"]],
        [["out0"], ["B"]],
      ]),
    ]);
  });

  const comp = new ConcurrentMachine({
    A: makeUnindexedCell(cellA),
    B: makeUnindexedCell(cellB),
    C: makeUnindexedCell(cellC),
    ctrl: controller,
  });

  // Wire cells A, B, and C to controller using prefix wiring
  let wired = new TraceMachine(comp, ["ctrl", "A"], ["A"]);
  wired = new TraceMachine(wired, ["ctrl", "B"], ["B"]);
  wired = new TraceMachine(wired, ["ctrl", "C"], ["C"]);

  return wired;
}

describe("Fibonacci Machine 2 (sequential assignment)", () => {
  it("returns sequential Fibonacci numbers on each 'ctrl.next' trigger", () => {
    const fib = new Runner(createFibonacciMachine2());

    // 1st trigger: return 1 (initial B)
    let res = fib.step({ channel: ["ctrl", "next"], value: null });
    expect(res).toEqual({
      kind: "read",
      channel: ["ctrl", "next"],
      value: null,
    });
    res = fib.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["ctrl", "out0", "set"],
      value: 1,
    });

    // Single propagation tick: runs add, shift1, shift2, and resets loop
    res = fib.step();
    expect(res).toEqual({ kind: "waiting" });

    // 2nd trigger: return 1 (value of B after 1st update)
    res = fib.step({ channel: ["ctrl", "next"], value: null });
    expect(res).toEqual({
      kind: "read",
      channel: ["ctrl", "next"],
      value: null,
    });
    res = fib.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["ctrl", "out0", "set"],
      value: 1,
    });

    res = fib.step();
    expect(res).toEqual({ kind: "waiting" });

    // 3rd trigger: return 2
    res = fib.step({ channel: ["ctrl", "next"], value: null });
    expect(res).toEqual({
      kind: "read",
      channel: ["ctrl", "next"],
      value: null,
    });
    res = fib.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["ctrl", "out0", "set"],
      value: 2,
    });

    res = fib.step();
    expect(res).toEqual({ kind: "waiting" });

    // 4th trigger: return 3
    res = fib.step({ channel: ["ctrl", "next"], value: null });
    expect(res).toEqual({
      kind: "read",
      channel: ["ctrl", "next"],
      value: null,
    });
    res = fib.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["ctrl", "out0", "set"],
      value: 3,
    });

    res = fib.step();
    expect(res).toEqual({ kind: "waiting" });

    // 5th trigger: return 5
    res = fib.step({ channel: ["ctrl", "next"], value: null });
    expect(res).toEqual({
      kind: "read",
      channel: ["ctrl", "next"],
      value: null,
    });
    res = fib.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["ctrl", "out0", "set"],
      value: 5,
    });

    res = fib.step();
    expect(res).toEqual({ kind: "waiting" });
  });
});

export function createMinMachine(): MachineInstance {
  const lessThan = new RenameMachine(new LessThanCellMachine(), [
    [["out0"], ["cond"]],
  ]);

  const choice = new ChoiceMachine({
    true: new SequenceMachine([
      new DiscardMachine(["cond", "true"]),
      new AssignCellMachine(),
    ]),
    false: new SequenceMachine([
      new DiscardMachine(["cond", "false"]),
      new RenameMachine(new AssignCellMachine(), [[["in0"], ["in1"]]]),
    ]),
  });

  const controller = new RenameMachine(
    new TraceMachine(
      new ConcurrentMachine({
        lessThan: lessThan,
        choice: choice,
      }),
      ["lessThan", "cond"],
      ["choice", "cond"],
    ),
    [
      [
        ["lessThan", "in0"],
        ["in0", "lessThan"],
      ],
      [
        ["lessThan", "in1"],
        ["in1", "lessThan"],
      ],
      [
        ["choice", "in0"],
        ["in0", "choice"],
      ],
      [
        ["choice", "in1"],
        ["in1", "choice"],
      ],
      [
        ["choice", "out0"],
        ["out0", "choice"],
      ],
    ],
  );

  return controller;
}

describe("MinSystem (conditional control flow example)", () => {
  it("computes minimum when A < B (true branch)", () => {
    const cellA = new ValueCellMachine(10);
    const cellB = new ValueCellMachine(20);
    const cellMin = new ValueCellMachine();
    const ctrl = createMinMachine();

    const comp = new ConcurrentMachine({
      in0: cellA,
      in1: cellB,
      out0: cellMin,
      ctrl: ctrl,
    });

    let wired = new TraceMachine(comp, ["ctrl", "in0"], ["in0"]);
    wired = new TraceMachine(wired, ["ctrl", "in1"], ["in1"]);
    wired = new TraceMachine(wired, ["ctrl", "out0"], ["out0"]);

    const runner = new Runner(wired);
    const res = runner.step();
    expect(res).toEqual({ kind: "done" });

    // A is 10, B is 20, so MIN should be 10 (value of A)
    const cellMinState = findStateForMachine(wired, runner.getState(), cellMin);
    expect(cellMin.getValue(cellMinState)).toBe(10);
  });

  it("computes minimum when A > B (false branch)", () => {
    const cellA = new ValueCellMachine(50);
    const cellB = new ValueCellMachine(20);
    const cellMin = new ValueCellMachine();
    const ctrl = createMinMachine();

    const comp = new ConcurrentMachine({
      in0: cellA,
      in1: cellB,
      out0: cellMin,
      ctrl: ctrl,
    });

    let wired = new TraceMachine(comp, ["ctrl", "in0"], ["in0"]);
    wired = new TraceMachine(wired, ["ctrl", "in1"], ["in1"]);
    wired = new TraceMachine(wired, ["ctrl", "out0"], ["out0"]);

    // Run the automated pipeline in one tick
    const runner = new Runner(wired);
    const res = runner.step();
    expect(res).toEqual({ kind: "done" });

    // A is 50, B is 20, so MIN should be 20 (value of B)
    const cellMinState = findStateForMachine(wired, runner.getState(), cellMin);
    expect(cellMin.getValue(cellMinState)).toBe(20);
  });
});
