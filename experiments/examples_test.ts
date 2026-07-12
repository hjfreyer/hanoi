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
  WriteConstantMachine,
  PrefixMachine,
} from "./impl";
import {
  ValueCellMachine,
  AssignCellMachine,
  AddCellMachine,
  LessThanCellMachine,
  StringLengthMachine,
  CharAtMachine,
} from "./primitives";
import { Runner, makeUnindexedCell } from "./testing";

export function createFibonacciMachine2(): MachineInstance {
  const cellA = new ValueCellMachine(0);
  const cellB = new ValueCellMachine(1);
  const cellC = new ValueCellMachine(1);

  const controller = new LoopMachine(() => {
    return new SequenceMachine([
      new PrefixMachine(
        ["env"],
        new SequenceMachine([
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
        ]),
      ),
      new WriteConstantMachine(["loop", "continue"], null),
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

export function createStringCharIterator(): MachineInstance {
  const cellIdx = new ValueCellMachine(0);
  const cellLen = new ValueCellMachine(0);
  const cellChar = new ValueCellMachine("");
  const cellOne = new ValueCellMachine(1);

  const controller = new SequenceMachine([
    // Initialize len = str.length
    new RenameMachine(new StringLengthMachine(), [
      [["in0", "copy"], ["str", "copy"]],
      [["in0", "value"], ["str", "value"]],
      [["out0", "set"], ["len", "set"]],
    ]),

    // Loop
    new LoopMachine(() => {
      return new SequenceMachine([
        new SequenceMachine([
          new DiscardMachine(["env", "next"]),
          new RenameMachine(
            new TraceMachine(
              new ConcurrentMachine({
                lessThan: new RenameMachine(new LessThanCellMachine(), [
                  [["in0", "copy"], ["idx", "copy"]],
                  [["in0", "value"], ["idx", "value"]],
                  [["in1", "copy"], ["len", "copy"]],
                  [["in1", "value"], ["len", "value"]],
                  [["out0"], ["cond"]],
                ]),
                choice: new ChoiceMachine({
                  true: new SequenceMachine([
                    new DiscardMachine(["cond", "true"]),
                    // Write some
                    new WriteConstantMachine(["env", "some"], null),

                    // Get character at idx
                    new RenameMachine(new CharAtMachine(), [
                      [["in0", "copy"], ["env", "str", "copy"]],
                      [["in0", "value"], ["env", "str", "value"]],
                      [["in1", "copy"], ["idx", "copy"]],
                      [["in1", "value"], ["idx", "value"]],
                      [["out0", "set"], ["char", "set"]],
                    ]),

                    // Increment idx: idx = idx + 1
                    new RenameMachine(new AddCellMachine(), [
                      [["in0", "copy"], ["idx", "copy"]],
                      [["in0", "value"], ["idx", "value"]],
                      [["in1", "copy"], ["one", "copy"]],
                      [["in1", "value"], ["one", "value"]],
                      [["out0", "set"], ["idx", "set"]],
                    ]),
                  ]),
                  false: new SequenceMachine([
                    new DiscardMachine(["cond", "false"]),
                    // Break out of the loop
                    new WriteConstantMachine(["loop", "break"], null),
                  ]),
                }),
              }),
              ["lessThan", "cond"],
              ["choice", "cond"],
            ),
            [
              [["lessThan", "idx"], ["env", "idx", "lessThan"]],
              [["lessThan", "len"], ["env", "len", "lessThan"]],
              [["choice", "idx"], ["env", "idx", "choice"]],
              [["choice", "char"], ["env", "char", "choice"]],
              [["choice", "one"], ["env", "one", "choice"]],
              [["choice", "env", "str"], ["env", "str"]],
              [["choice", "env", "some"], ["env", "some"]],
              [["choice", "loop"], ["loop"]],
            ],
          ),
        ]),
        // loop continue
        new WriteConstantMachine(["loop", "continue"], null),
      ]);
    }),

    // After loop terminates: write none directly
    new WriteConstantMachine(["none"], null),
  ]);

  const comp = new ConcurrentMachine({
    idx: makeUnindexedCell(cellIdx),
    len: makeUnindexedCell(cellLen),
    char: makeUnindexedCell(cellChar),
    one: makeUnindexedCell(cellOne),
    ctrl: controller,
  });

  // Wire internal cells to ctrl
  let wired = new TraceMachine(comp, ["ctrl", "idx"], ["idx"]);
  wired = new TraceMachine(wired, ["ctrl", "len"], ["len"]);
  wired = new TraceMachine(wired, ["ctrl", "char", "choice", "set"], ["char", "set"]);
  wired = new TraceMachine(wired, ["ctrl", "one"], ["one"]);

  return new RenameMachine(wired, [
    [["ctrl", "next"], ["next"]],
    [["ctrl", "some"], ["some"]],
    [["ctrl", "none"], ["none"]],
    [["char", "copy"], ["value", "copy"]],
    [["char", "value"], ["value", "value"]],
    [["ctrl", "str", "copy"], ["str", "copy"]],
    [["ctrl", "str", "value"], ["str", "value"]],
  ]);
}

describe("String Character Iterator", () => {
  it("iterates over a non-empty string", () => {
    const strCell = new ValueCellMachine("cat");
    const iterator = createStringCharIterator();
    const system = new ConcurrentMachine({
      str: makeUnindexedCell(strCell),
      iter: iterator,
    });
    // Wire str to iter.str
    let wired = new TraceMachine(system, ["iter", "str"], ["str"]);
    const runner = new Runner(wired);

    // Initial state: not started. Runs StringLength (internal) and blocks on first read("next")
    expect(runner.run()).toEqual([]);

    // 1st iteration: trigger next, then read value "c"
    expect(runner.run({ channel: ["iter", "next"], value: null })).toEqual([
      { kind: "read", channel: ["iter", "next"], value: null },
      { kind: "write", channel: ["iter", "some"], value: null },
    ]);
    expect(runner.run({ channel: ["iter", "value", "copy"], value: null })).toEqual([
      { kind: "read", channel: ["iter", "value", "copy"], value: null },
      { kind: "write", channel: ["iter", "value", "value"], value: "c" },
    ]);

    // 2nd iteration: trigger next, then read value "a"
    expect(runner.run({ channel: ["iter", "next"], value: null })).toEqual([
      { kind: "read", channel: ["iter", "next"], value: null },
      { kind: "write", channel: ["iter", "some"], value: null },
    ]);
    expect(runner.run({ channel: ["iter", "value", "copy"], value: null })).toEqual([
      { kind: "read", channel: ["iter", "value", "copy"], value: null },
      { kind: "write", channel: ["iter", "value", "value"], value: "a" },
    ]);

    // 3rd iteration: trigger next, then read value "t"
    expect(runner.run({ channel: ["iter", "next"], value: null })).toEqual([
      { kind: "read", channel: ["iter", "next"], value: null },
      { kind: "write", channel: ["iter", "some"], value: null },
    ]);
    expect(runner.run({ channel: ["iter", "value", "copy"], value: null })).toEqual([
      { kind: "read", channel: ["iter", "value", "copy"], value: null },
      { kind: "write", channel: ["iter", "value", "value"], value: "t" },
    ]);

    // End of loop: trigger next, yields none and completes
    expect(runner.run({ channel: ["iter", "next"], value: null })).toEqual([
      { kind: "read", channel: ["iter", "next"], value: null },
      { kind: "write", channel: ["iter", "none"], value: null },
      { kind: "done" },
    ]);
  });

  it("iterates over an empty string", () => {
    const strCell = new ValueCellMachine("");
    const iterator = createStringCharIterator();
    const system = new ConcurrentMachine({
      str: makeUnindexedCell(strCell),
      iter: iterator,
    });
    // Wire str to iter.str
    let wired = new TraceMachine(system, ["iter", "str"], ["str"]);
    const runner = new Runner(wired);

    let stepRes = runner.step();
    expect(stepRes).toEqual({ kind: "waiting" });

    stepRes = runner.step({ channel: ["iter", "next"], value: null });
    expect(stepRes).toEqual({ kind: "read", channel: ["iter", "next"], value: null });

    stepRes = runner.step();
    expect(stepRes).toEqual({ kind: "write", channel: ["iter", "none"], value: null });

    stepRes = runner.step();
    expect(stepRes).toEqual({ kind: "done" });
  });

  it("iterates over an empty string using run()", () => {
    const strCell = new ValueCellMachine("");
    const iterator = createStringCharIterator();
    const system = new ConcurrentMachine({
      str: makeUnindexedCell(strCell),
      iter: iterator,
    });
    let wired = new TraceMachine(system, ["iter", "str"], ["str"]);
    const runner = new Runner(wired);

    // Initial run: executes initialization (StringLength) and stops when waiting on next
    expect(runner.run()).toEqual([]);

    // Trigger next: runs until it hits waiting (or done in this case because string is empty)
    expect(runner.run({ channel: ["iter", "next"], value: null })).toEqual([
      { kind: "read", channel: ["iter", "next"], value: null },
      { kind: "write", channel: ["iter", "none"], value: null },
      { kind: "done" },
    ]);
  });
});
