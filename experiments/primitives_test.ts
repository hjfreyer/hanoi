import {
  parseTranscript,
  checkTranscript,
  compileToSpec,
  sequence,
  read,
  write,
} from "./spec";
import {
  ConcurrentMachine,
  TraceMachine,
  SequenceMachine,
  WriteConstantMachine,
  RenameMachine,
  findStateForMachine,
} from "./impl";
import {
  ValueCellSpec,
  UninitValueCellSpec,
  ValueCellMachine,
  AddSpec,
  AddMachine,
  LessThanMachine,
  LessThanSpec,
  LessThanCellMachine,
  BinaryPredicateMachine,
  BinaryPredicateCellMachine,
  AddCellMachine,
  TestSpec,
  TestMachine,
  createIterSpec,
  StringLengthMachine,
  StringLengthSpec,
  CharAtMachine,
  CharAtSpec,
  AreEqualMachine,
  AreEqualSpec,
  AreEqualCellMachine,
} from "./primitives";
import { Runner, makeUnindexedCell } from "./testing";

describe("ValueCell example", () => {
  it("can set and copy values step-by-step", () => {
    const machine = new Runner(new ValueCellMachine(42));

    // Initially copy should return 42
    let res = machine.step({ channel: ["p0", "copy"], value: null });
    expect(res).toEqual({ kind: "read", channel: ["p0", "copy"], value: null });

    res = machine.step();
    expect(res).toEqual({ kind: "write", channel: ["p0", "value"], value: 42 });

    // Set value to 100
    res = machine.step({ channel: ["p1", "set"], value: 100 });
    expect(res).toEqual({ kind: "read", channel: ["p1", "set"], value: 100 });

    // Copy should now return 100
    res = machine.step({ channel: ["p0", "copy"], value: null });
    expect(res).toEqual({ kind: "read", channel: ["p0", "copy"], value: null });

    res = machine.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["p0", "value"],
      value: 100,
    });
  });

  it("verifies a valid execution transcript against ValueCellSpec", () => {
    const transcript = parseTranscript(`
            < p0.copy
            > p0.value
            < p1.set
            < p0.copy
            > p0.value
        `);
    expect(checkTranscript(compileToSpec(ValueCellSpec), transcript)).toBe(
      true,
    );
  });
});

describe("UninitValueCell example", () => {
  it("fails if machine tries to copy before set", () => {
    const machine = new Runner(new ValueCellMachine());
    // Trying to step copy before setting should not be accepted/should return waiting
    const res = machine.step({ channel: ["p0", "copy"], value: null });
    expect(res).toEqual({ kind: "waiting" });
  });

  it("can set first and then copy", () => {
    const machine = new Runner(new ValueCellMachine());

    // Set value to 25
    let res = machine.step({ channel: ["p0", "set"], value: 25 });
    expect(res).toEqual({ kind: "read", channel: ["p0", "set"], value: 25 });

    // Now copy should succeed and return 25
    res = machine.step({ channel: ["p1", "copy"], value: null });
    expect(res).toEqual({ kind: "read", channel: ["p1", "copy"], value: null });

    res = machine.step();
    expect(res).toEqual({ kind: "write", channel: ["p1", "value"], value: 25 });
  });

  it("verifies transcripts against UninitValueCellSpec", () => {
    const valid = parseTranscript(`
            < p0.set
            < p1.copy
            > p1.value
        `);
    expect(checkTranscript(compileToSpec(UninitValueCellSpec), valid)).toBe(
      true,
    );

    const invalid = parseTranscript(`
            < p0.copy
            > p0.value
            < p1.set
        `);
    expect(checkTranscript(compileToSpec(UninitValueCellSpec), invalid)).toBe(
      false,
    );
  });
});

describe("AddMachine example", () => {
  it("can read in0 and in1 in any order and writes sum to out0", () => {
    const machine = new Runner(new AddMachine());
    expect(machine.isCompleted()).toBe(false);
    expect(machine.step()).toEqual({ kind: "waiting" });

    expect(machine.step({ channel: ["in0"], value: 15 })).toEqual({
      kind: "read",
      channel: ["in0"],
      value: 15,
    });
    expect(machine.step()).toEqual({ kind: "waiting" });

    expect(machine.step({ channel: ["in1"], value: 25 })).toEqual({
      kind: "read",
      channel: ["in1"],
      value: 25,
    });
    expect(machine.step()).toEqual({
      kind: "write",
      channel: ["out0"],
      value: 40,
    });
    expect(machine.isCompleted()).toBe(true);
    expect(machine.step()).toEqual({ kind: "done" });
  });

  it("verifies transcripts against passive AddSpec", () => {
    const valid = parseTranscript(`
            < in0
            < in1
            > out0
        `);
    expect(checkTranscript(compileToSpec(AddSpec), valid)).toBe(true);
  });
});

describe("Automated AddMachine Wiring", () => {
  it("wires driver, passive AddMachine, and ValueCells to execute automated sum computation in one step", () => {
    const cellIn0 = new ValueCellMachine(10);
    const cellIn1 = new ValueCellMachine(20);
    const cellOut0 = new ValueCellMachine();
    const add = new AddMachine();

    // Construct a driver that simply triggers the copies on in0 and in1 cells in sequence
    const driver = new SequenceMachine([
      new WriteConstantMachine(["in0", "copy"], null),
      new WriteConstantMachine(["in1", "copy"], null),
    ]);

    const comp = new ConcurrentMachine({
      system: new ConcurrentMachine({
        in0: makeUnindexedCell(cellIn0),
        in1: makeUnindexedCell(cellIn1),
        out0: makeUnindexedCell(cellOut0),
        add: add,
      }),
      driver: driver,
    });

    // 1. Wire the system internally:
    // cellIn0.value -> add.in0
    let systemWired = new TraceMachine(
      comp,
      ["system", "in0", "value"],
      ["system", "add", "in0"],
    );
    // cellIn1.value -> add.in1
    systemWired = new TraceMachine(
      systemWired,
      ["system", "in1", "value"],
      ["system", "add", "in1"],
    );
    // add.out0 -> cellOut0.set
    systemWired = new TraceMachine(
      systemWired,
      ["system", "add", "out0"],
      ["system", "out0", "set"],
    );

    // 2. Wire the driver to the system:
    // driver.in0.copy -> system.in0.copy, driver.in1.copy -> system.in1.copy
    let wired = new TraceMachine(systemWired, ["driver"], ["system"]);

    // Execute the entire pipeline in one single step!
    // It runs silently and terminates since there are no more active writes.
    const runner = new Runner(wired);
    const res = runner.step();
    expect(res).toEqual({ kind: "done" });
    expect(runner.isCompleted()).toBe(true);

    // Verify cellOut0 has stored the correct sum of 30!
    const cellOut0State = findStateForMachine(
      wired,
      runner.getState(),
      cellOut0,
    );
    expect(cellOut0.getValue(cellOut0State)).toBe(30);
  });
});

describe("LessThanMachine example", () => {
  it("compares x and y and writes to true or false", () => {
    // Test case 1: x < y is true
    {
      const machine = new Runner(new LessThanMachine());
      expect(machine.isCompleted()).toBe(false);
      expect(machine.step()).toEqual({ kind: "waiting" });
      expect(machine.step({ channel: ["in0"], value: 10 })).toEqual({
        kind: "read",
        channel: ["in0"],
        value: 10,
      });
      expect(machine.step({ channel: ["in1"], value: 20 })).toEqual({
        kind: "read",
        channel: ["in1"],
        value: 20,
      });
      expect(machine.step()).toEqual({
        kind: "write",
        channel: ["out0", "true"],
        value: null,
      });
      expect(machine.isCompleted()).toBe(true);
    }

    // Test case 2: in0 < in1 is false
    {
      const machine = new Runner(new LessThanMachine());
      expect(machine.step({ channel: ["in0"], value: 50 })).toEqual({
        kind: "read",
        channel: ["in0"],
        value: 50,
      });
      expect(machine.step({ channel: ["in1"], value: 20 })).toEqual({
        kind: "read",
        channel: ["in1"],
        value: 20,
      });
      expect(machine.step()).toEqual({
        kind: "write",
        channel: ["out0", "false"],
        value: null,
      });
      expect(machine.isCompleted()).toBe(true);
    }
  });

  it("verifies transcripts against LessThanSpec", () => {
    const validTrue = parseTranscript(`
            < in0
            < in1
            > out0.true
        `);
    expect(checkTranscript(compileToSpec(LessThanSpec), validTrue)).toBe(true);

    const validFalse = parseTranscript(`
            < in1
            < in0
            > out0.false
        `);
    expect(checkTranscript(compileToSpec(LessThanSpec), validFalse)).toBe(true);

    const invalid = parseTranscript(`
            < in0
            < in1
            > out0.true
            > out0.false
        `);
    expect(checkTranscript(compileToSpec(LessThanSpec), invalid)).toBe(false);
  });
});

describe("BinaryPredicateMachine example (Equals)", () => {
  it("compares in0 and in1 and writes true/false output", () => {
    // Equal case
    {
      const machine = new Runner(new BinaryPredicateMachine((x, y) => x === y));
      expect(machine.step({ channel: ["in0"], value: 10 })).toEqual({
        kind: "read",
        channel: ["in0"],
        value: 10,
      });
      expect(machine.step({ channel: ["in1"], value: 10 })).toEqual({
        kind: "read",
        channel: ["in1"],
        value: 10,
      });
      expect(machine.step()).toEqual({
        kind: "write",
        channel: ["out0", "true"],
        value: null,
      });
    }
    // Not equal case
    {
      const machine = new Runner(new BinaryPredicateMachine((x, y) => x === y));
      expect(machine.step({ channel: ["in0"], value: 10 })).toEqual({
        kind: "read",
        channel: ["in0"],
        value: 10,
      });
      expect(machine.step({ channel: ["in1"], value: 20 })).toEqual({
        kind: "read",
        channel: ["in1"],
        value: 20,
      });
      expect(machine.step()).toEqual({
        kind: "write",
        channel: ["out0", "false"],
        value: null,
      });
    }
  });
});

describe("AddCellMachine", () => {
  it("requests copy from cell In0 and cell In1, and writes the sum to cell Out0", () => {
    const cellIn0 = new ValueCellMachine(10);
    const cellIn1 = new ValueCellMachine(20);
    const cellOut0 = new ValueCellMachine();
    const add = new AddCellMachine();

    const comp = new ConcurrentMachine({
      in0: makeUnindexedCell(cellIn0),
      in1: makeUnindexedCell(cellIn1),
      out0: makeUnindexedCell(cellOut0),
      add: add,
    });

    let wired = new TraceMachine(comp, ["add", "in0"], ["in0"]);
    wired = new TraceMachine(wired, ["add", "in1"], ["in1"]);
    wired = new TraceMachine(wired, ["add", "out0"], ["out0"]);

    const runner = new Runner(wired);
    const res = runner.step();
    expect(res).toEqual({ kind: "done" });

    const cellOut0State = findStateForMachine(
      wired,
      runner.getState(),
      cellOut0,
    );
    expect(cellOut0.getValue(cellOut0State)).toBe(30);
  });
});

describe("LessThanCellMachine", () => {
  it("requests copy from cell In0 and cell In1, and writes null to cell True or cell False", () => {
    // Case 1: 10 < 20 (true)
    {
      const cellIn0 = new ValueCellMachine(10);
      const cellIn1 = new ValueCellMachine(20);
      const cellTrue = new ValueCellMachine();
      const cellFalse = new ValueCellMachine();
      const lessThan = new LessThanCellMachine();

      const comp = new ConcurrentMachine({
        in0: makeUnindexedCell(cellIn0),
        in1: makeUnindexedCell(cellIn1),
        t: makeUnindexedCell(cellTrue),
        f: makeUnindexedCell(cellFalse),
        lessThan: lessThan,
      });

      let wired = new TraceMachine(comp, ["lessThan", "in0"], ["in0"]);
      wired = new TraceMachine(wired, ["lessThan", "in1"], ["in1"]);
      wired = new TraceMachine(
        wired,
        ["lessThan", "out0", "true"],
        ["t", "set"],
      );
      wired = new TraceMachine(
        wired,
        ["lessThan", "out0", "false"],
        ["f", "set"],
      );

      const runner = new Runner(wired);
      const res = runner.step();
      expect(res).toEqual({ kind: "waiting" });

      const cellTrueState = findStateForMachine(
        wired,
        runner.getState(),
        cellTrue,
      );
      expect(cellTrue.getValue(cellTrueState)).toBe(null);

      const cellFalseState = findStateForMachine(
        wired,
        runner.getState(),
        cellFalse,
      );
      expect(cellFalse.getValue(cellFalseState)).toBeUndefined();
    }

    // Case 2: 50 < 20 (false)
    {
      const cellIn0 = new ValueCellMachine(50);
      const cellIn1 = new ValueCellMachine(20);
      const cellTrue = new ValueCellMachine();
      const cellFalse = new ValueCellMachine();
      const lessThan = new LessThanCellMachine();

      const comp = new ConcurrentMachine({
        in0: makeUnindexedCell(cellIn0),
        in1: makeUnindexedCell(cellIn1),
        t: makeUnindexedCell(cellTrue),
        f: makeUnindexedCell(cellFalse),
        lessThan: lessThan,
      });

      let wired = new TraceMachine(comp, ["lessThan", "in0"], ["in0"]);
      wired = new TraceMachine(wired, ["lessThan", "in1"], ["in1"]);
      wired = new TraceMachine(
        wired,
        ["lessThan", "out0", "true"],
        ["t", "set"],
      );
      wired = new TraceMachine(
        wired,
        ["lessThan", "out0", "false"],
        ["f", "set"],
      );

      const runner = new Runner(wired);
      const res = runner.step();
      expect(res).toEqual({ kind: "waiting" });

      const cellTrueState = findStateForMachine(
        wired,
        runner.getState(),
        cellTrue,
      );
      expect(cellTrue.getValue(cellTrueState)).toBeUndefined();

      const cellFalseState = findStateForMachine(
        wired,
        runner.getState(),
        cellFalse,
      );
      expect(cellFalse.getValue(cellFalseState)).toBe(null);
    }
  });
});

describe("TestMachine", () => {
  it("outputs true when input is true", () => {
    const machine = new Runner(new TestMachine());
    expect(machine.isCompleted()).toBe(false);

    expect(machine.step()).toEqual({ kind: "waiting" });

    expect(machine.step({ channel: ["input"], value: true })).toEqual({
      kind: "read",
      channel: ["input"],
      value: true,
    });

    expect(machine.step()).toEqual({
      kind: "write",
      channel: ["out0", "true"],
      value: null,
    });

    expect(machine.isCompleted()).toBe(true);
    expect(machine.step()).toEqual({ kind: "done" });
  });

  it("outputs false when input is false", () => {
    const machine = new Runner(new TestMachine());
    expect(machine.isCompleted()).toBe(false);

    expect(machine.step({ channel: ["input"], value: false })).toEqual({
      kind: "read",
      channel: ["input"],
      value: false,
    });

    expect(machine.step()).toEqual({
      kind: "write",
      channel: ["out0", "false"],
      value: null,
    });

    expect(machine.isCompleted()).toBe(true);
  });

  it("verifies transcripts against TestSpec", () => {
    const validTrue = parseTranscript(`
            < input
            > out0.true
        `);
    expect(checkTranscript(compileToSpec(TestSpec), validTrue)).toBe(true);

    const validFalse = parseTranscript(`
            < input
            > out0.false
        `);
    expect(checkTranscript(compileToSpec(TestSpec), validFalse)).toBe(true);

    const invalid = parseTranscript(`
            < input
            > out0.true
            > out0.false
        `);
    expect(checkTranscript(compileToSpec(TestSpec), invalid)).toBe(false);
  });
});

describe("createIterSpec", () => {
  it("creates an iterator spec that reads next, writes some and performs spec, and stops after none", () => {
    const spec = sequence(read(["copy"]), write(["value"]));
    const iterSpec = compileToSpec(createIterSpec(spec));

    // Valid: 2 iterations, then none, and stop
    const valid = parseTranscript(`
      < next
      > some
      < value.copy
      > value.value
      < next
      > some
      < value.copy
      > value.value
      < next
      > none
    `);
    expect(checkTranscript(iterSpec, valid)).toBe(true);

    // Invalid: performing input after none
    const invalidAfterNone = parseTranscript(`
      < next
      > none
      < next
    `);
    expect(checkTranscript(iterSpec, invalidAfterNone)).toBe(false);

    // Invalid: performing value copy after none
    const invalidCopyAfterNone = parseTranscript(`
      < next
      > none
      < value.copy
    `);
    expect(checkTranscript(iterSpec, invalidCopyAfterNone)).toBe(false);

    // Valid: 0 iterations (just none)
    const zeroIterations = parseTranscript(`
      < next
      > none
    `);
    expect(checkTranscript(iterSpec, zeroIterations)).toBe(true);

    // Forbidden: another next and none after none
    const forbiddenDoubleNone = parseTranscript(`
      < next
      > none
      < next
      > none
    `);
    expect(checkTranscript(iterSpec, forbiddenDoubleNone)).toBe(false);
  });
});

describe("StringLengthMachine", () => {
  it("requests copy from in0 cell, reads its string value, and writes the length to out0", () => {
    const machine = new Runner(new StringLengthMachine());
    expect(machine.isCompleted()).toBe(false);

    // Step 1: writes copy command to in0
    let res = machine.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["in0", "copy"],
      value: null,
    });

    // Step 2: reads the value from in0
    res = machine.step({ channel: ["in0", "value"], value: "hello" });
    expect(res).toEqual({
      kind: "read",
      channel: ["in0", "value"],
      value: "hello",
    });

    // Step 3: writes the length (5) to out0
    res = machine.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["out0", "set"],
      value: 5,
    });

    expect(machine.isCompleted()).toBe(true);
    expect(machine.step()).toEqual({ kind: "done" });
  });

  it("verifies valid transcripts against StringLengthSpec", () => {
    const valid = parseTranscript(`
      > in0.copy
      < in0.value
      > out0.set
    `);
    expect(checkTranscript(compileToSpec(StringLengthSpec), valid)).toBe(true);
  });

  it("throws an error when a non-string value is read", () => {
    const machine = new Runner(new StringLengthMachine());
    machine.step(); // write copy
    machine.step({ channel: ["in0", "value"], value: 123 }); // read number 123
    expect(() => {
      machine.step(); // try to step (computes length)
    }).toThrow("Value is not a string");
  });
});

describe("CharAtMachine", () => {
  it("requests copy from in0 and in1, reads value from both, and writes charAt index to out0", () => {
    const machine = new Runner(new CharAtMachine());
    expect(machine.isCompleted()).toBe(false);

    // Initial state: outputs two copy writes in concurrent
    let res = machine.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["in0", "copy"],
      value: null,
    });

    res = machine.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["in1", "copy"],
      value: null,
    });

    // Step 2: reads the value from both cells
    res = machine.step({ channel: ["in0", "value"], value: "banana" });
    expect(res).toEqual({
      kind: "read",
      channel: ["in0", "value"],
      value: "banana",
    });

    res = machine.step({ channel: ["in1", "value"], value: 3 });
    expect(res).toEqual({
      kind: "read",
      channel: ["in1", "value"],
      value: 3,
    });

    // Step 3: writes the charAt value ("a") to out0
    res = machine.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["out0", "set"],
      value: "a",
    });

    expect(machine.isCompleted()).toBe(true);
    expect(machine.step()).toEqual({ kind: "done" });
  });

  it("verifies valid transcripts against CharAtSpec", () => {
    const valid = parseTranscript(`
      > in0.copy
      > in1.copy
      < in0.value
      < in1.value
      > out0.set
    `);
    expect(checkTranscript(compileToSpec(CharAtSpec), valid)).toBe(true);
  });

  it("throws an error when non-string value is passed as first argument", () => {
    const machine = new Runner(new CharAtMachine());
    machine.step(); // write in0 copy
    machine.step(); // write in1 copy
    machine.step({ channel: ["in0", "value"], value: 123 }); // non-string value
    machine.step({ channel: ["in1", "value"], value: 0 }); // index
    expect(() => {
      machine.step();
    }).toThrow("First argument must be a string");
  });

  it("throws an error when non-integer index is passed", () => {
    const machine = new Runner(new CharAtMachine());
    machine.step(); // write in0 copy
    machine.step(); // write in1 copy
    machine.step({ channel: ["in0", "value"], value: "banana" }); // string
    machine.step({ channel: ["in1", "value"], value: 1.5 }); // non-integer index
    expect(() => {
      machine.step();
    }).toThrow("Second argument must be an integer");
  });
});

describe("AreEqualMachine and AreEqualCellMachine", () => {
  it("AreEqualMachine compares x and y and writes true/false output", () => {
    // Equal case
    {
      const machine = new Runner(new AreEqualMachine());
      expect(machine.step({ channel: ["in0"], value: 100 })).toEqual({
        kind: "read",
        channel: ["in0"],
        value: 100,
      });
      expect(machine.step({ channel: ["in1"], value: 100 })).toEqual({
        kind: "read",
        channel: ["in1"],
        value: 100,
      });
      expect(machine.step()).toEqual({
        kind: "write",
        channel: ["out0", "true"],
        value: null,
      });
    }

    // Not equal case
    {
      const machine = new Runner(new AreEqualMachine());
      machine.step({ channel: ["in0"], value: 100 });
      machine.step({ channel: ["in1"], value: 200 });
      expect(machine.step()).toEqual({
        kind: "write",
        channel: ["out0", "false"],
        value: null,
      });
    }
  });

  it("verifies valid transcripts against AreEqualSpec", () => {
    const valid = parseTranscript(`
      < in0
      < in1
      > out0.true
    `);
    expect(checkTranscript(compileToSpec(AreEqualSpec), valid)).toBe(true);
  });

  it("AreEqualCellMachine requests copy from cell in0 and in1, and writes true/false to cell out0", () => {
    const cellIn0 = new ValueCellMachine(42);
    const cellIn1 = new ValueCellMachine(42);
    const cellTrue = new ValueCellMachine();
    const cellFalse = new ValueCellMachine();
    const eq = new AreEqualCellMachine();

    const comp = new ConcurrentMachine({
      in0: makeUnindexedCell(cellIn0),
      in1: makeUnindexedCell(cellIn1),
      t: makeUnindexedCell(cellTrue),
      f: makeUnindexedCell(cellFalse),
      eq: eq,
    });

    let wired = new TraceMachine(comp, ["eq", "in0"], ["in0"]);
    wired = new TraceMachine(wired, ["eq", "in1"], ["in1"]);
    wired = new TraceMachine(wired, ["eq", "out0", "true"], ["t", "set"]);
    wired = new TraceMachine(wired, ["eq", "out0", "false"], ["f", "set"]);

    const runner = new Runner(wired);
    const res = runner.step();
    expect(res).toEqual({ kind: "waiting" });

    const cellTrueState = findStateForMachine(
      wired,
      runner.getState(),
      cellTrue,
    );
    expect(cellTrue.getValue(cellTrueState)).toBe(null);

    const cellFalseState = findStateForMachine(
      wired,
      runner.getState(),
      cellFalse,
    );
    expect(cellFalse.getValue(cellFalseState)).toBeUndefined();
  });
});
