import {
  MachineSpec,
  sequence,
  read,
  write,
  choice,
  loop,
  concurrent,
  transition,
  isCompleted,
  getPossibleTransitions,
  indexed,
  rename,
  prefix,
  trace,
} from "./spec";
import { MachineInstance, StepResult, channelsEqual } from "./impl";

// 1. Define the ValueCell specs
export const ValueCellSpec = indexed(
  choice({
    set: read(["set"]),
    copy: sequence(read(["copy"]), write(["value"])),
  }),
);

export const UninitValueCellSpec = sequence(
  indexed(read(["set"])),
  indexed(
    choice({
      set: read(["set"]),
      copy: sequence(read(["copy"]), write(["value"])),
    }),
  ),
);

// 2. Implement the unified ValueCellMachine using MachineInstance
export class ValueCellMachine implements MachineInstance {
  constructor(private initialValue?: any) {}

  createState(): any {
    return {
      value: this.initialValue,
      pendingWriteIndex: undefined,
    };
  }

  getValue(state: any): any {
    return state.value;
  }

  getSpec(): MachineSpec {
    return this.initialValue !== undefined
      ? ValueCellSpec
      : UninitValueCellSpec;
  }

  isCompleted(state: any): boolean {
    return state.value !== undefined && state.pendingWriteIndex === undefined;
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (action) {
      const lastSegment = action.channel[action.channel.length - 1];
      const prefix = action.channel.slice(0, -1);
      if (lastSegment === "set") {
        return {
          result: {
            kind: "read",
            channel: action.channel,
            value: action.value,
          },
          state: {
            value: action.value,
            pendingWriteIndex: undefined,
          },
        };
      }
      if (lastSegment === "copy" && state.value !== undefined) {
        return {
          result: {
            kind: "read",
            channel: action.channel,
            value: action.value,
          },
          state: {
            ...state,
            pendingWriteIndex: prefix,
          },
        };
      }
      return { result: { kind: "waiting" }, state };
    }

    if (state.pendingWriteIndex !== undefined) {
      return {
        result: {
          kind: "write",
          channel: [...state.pendingWriteIndex, "value"],
          value: state.value,
        },
        state: {
          ...state,
          pendingWriteIndex: undefined,
        },
      };
    }

    return { result: { kind: "waiting" }, state };
  }
}

// 3. Define the BinaryValue spec (reads in0 and in1, then writes out0)
export const BinaryValueSpec = sequence(
  concurrent({
    in0: read([]),
    in1: read([]),
  }),
  write(["out0"]),
);

export const AddSpec = BinaryValueSpec;

// 4. Implement the BinaryValueMachine using MachineInstance
export class BinaryValueMachine implements MachineInstance {
  constructor(private op: (x: any, y: any) => any) {}

  createState(): any {
    return {
      xVal: undefined,
      yVal: undefined,
      state: "waiting",
    };
  }

  getSpec(): MachineSpec {
    return BinaryValueSpec;
  }

  isCompleted(state: any): boolean {
    return state.state === "done";
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "waiting") {
      if (!action) {
        return { result: { kind: "waiting" }, state };
      }
      if (action.channel[0] === "in0") {
        const nextState = {
          ...state,
          xVal: action.value,
        };
        const finalState = this.checkReady(nextState);
        return {
          result: { kind: "read", channel: ["in0"], value: action.value },
          state: finalState,
        };
      }
      if (action.channel[0] === "in1") {
        const nextState = {
          ...state,
          yVal: action.value,
        };
        const finalState = this.checkReady(nextState);
        return {
          result: { kind: "read", channel: ["in1"], value: action.value },
          state: finalState,
        };
      }
      throw new Error(`Invalid channel: ${action.channel}`);
    } else if (state.state === "ready_z") {
      return {
        result: {
          kind: "write",
          channel: ["out0"],
          value: this.op(state.xVal, state.yVal),
        },
        state: {
          ...state,
          state: "done",
        },
      };
    }
    return { result: { kind: "done" }, state };
  }

  private checkReady(state: any): any {
    if (state.xVal !== undefined && state.yVal !== undefined) {
      return {
        ...state,
        state: "ready_z",
      };
    }
    return state;
  }
}

export class AddMachine extends BinaryValueMachine {
  constructor() {
    super((x, y) => x + y);
  }
}

export const BinaryPredicateSpec = sequence(
  concurrent({
    in0: read([]),
    in1: read([]),
  }),
  choice({
    true: write(["out0", "true"]),
    false: write(["out0", "false"]),
  }),
);

export const LessThanSpec = BinaryPredicateSpec;

export class BinaryPredicateMachine implements MachineInstance {
  constructor(private pred: (x: any, y: any) => boolean) {}

  createState(): any {
    return {
      xVal: undefined,
      yVal: undefined,
      state: "waiting",
    };
  }

  getSpec(): MachineSpec {
    return BinaryPredicateSpec;
  }

  isCompleted(state: any): boolean {
    return state.state === "done";
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "waiting") {
      if (!action) {
        return { result: { kind: "waiting" }, state };
      }
      if (action.channel[0] === "in0") {
        const nextState = {
          ...state,
          xVal: action.value,
        };
        const finalState = this.checkReady(nextState);
        return {
          result: { kind: "read", channel: ["in0"], value: action.value },
          state: finalState,
        };
      }
      if (action.channel[0] === "in1") {
        const nextState = {
          ...state,
          yVal: action.value,
        };
        const finalState = this.checkReady(nextState);
        return {
          result: { kind: "read", channel: ["in1"], value: action.value },
          state: finalState,
        };
      }
      throw new Error(`Invalid channel: ${action.channel}`);
    } else if (state.state === "ready_output") {
      const outChan = this.pred(state.xVal, state.yVal)
        ? ["out0", "true"]
        : ["out0", "false"];
      return {
        result: { kind: "write", channel: outChan, value: null },
        state: {
          ...state,
          state: "done",
        },
      };
    }
    return { result: { kind: "done" }, state };
  }

  private checkReady(state: any): any {
    if (state.xVal !== undefined && state.yVal !== undefined) {
      return {
        ...state,
        state: "ready_output",
      };
    }
    return state;
  }
}

export class LessThanMachine extends BinaryPredicateMachine {
  constructor() {
    super((x, y) => x < y);
  }
}

export const AreEqualSpec = BinaryPredicateSpec;

export class AreEqualMachine extends BinaryPredicateMachine {
  constructor() {
    super((x, y) => x === y);
  }
}

// 5. Implement UnaryCellMachine and AssignCellMachine
export const UnaryCellSpec = sequence(
  write(["in0", "copy"]),
  read(["in0", "value"]),
  write(["out0", "set"]),
);

export class UnaryCellMachine implements MachineInstance {
  private copyChan = ["in0", "copy"];
  private readChan = ["in0", "value"];
  private setChan = ["out0", "set"];

  constructor(private op: (val: any) => any) {}

  createState(): any {
    return {
      state: "copying",
      val: undefined,
    };
  }

  getSpec(): MachineSpec {
    return UnaryCellSpec;
  }

  isCompleted(state: any): boolean {
    return state.state === "done";
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "copying") {
      return {
        result: { kind: "write", channel: this.copyChan, value: null },
        state: {
          ...state,
          state: "reading",
        },
      };
    }

    if (state.state === "reading") {
      if (!action || !channelsEqual(action.channel, this.readChan)) {
        return { result: { kind: "waiting" }, state };
      }
      return {
        result: { kind: "read", channel: this.readChan, value: action.value },
        state: {
          ...state,
          val: action.value,
          state: "writing",
        },
      };
    }

    if (state.state === "writing") {
      return {
        result: {
          kind: "write",
          channel: this.setChan,
          value: this.op(state.val),
        },
        state: {
          ...state,
          state: "done",
        },
      };
    }

    return { result: { kind: "done" }, state };
  }
}

export class AssignCellMachine extends UnaryCellMachine {
  constructor() {
    super((val) => val);
  }
}

// 6. Implement BinaryCellMachine and AddCellMachine
export class BinaryCellMachine implements MachineInstance {
  constructor(private op: (x: any, y: any) => any) {}

  createState(): any {
    return {
      in0State: "writing_copy", // "writing_copy" | "reading" | "done"
      in1State: "writing_copy", // "writing_copy" | "reading" | "done"
      xVal: 0,
      yVal: 0,
      state: "reading_phase", // "reading_phase" | "writing_phase" | "done"
    };
  }

  getSpec(): MachineSpec {
    return sequence(
      concurrent({
        in0: sequence(write(["copy"]), read(["value"])),
        in1: sequence(write(["copy"]), read(["value"])),
      }),
      write(["out0", "set"]),
    );
  }

  isCompleted(state: any): boolean {
    return state.state === "done";
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "reading_phase") {
      if (action) {
        const key = action.channel[0];
        const last = action.channel[action.channel.length - 1];
        if (key === "in0" && last === "value" && state.in0State === "reading") {
          const nextIn0State = "done";
          const isAllDone =
            nextIn0State === "done" && state.in1State === "done";
          return {
            result: {
              kind: "read",
              channel: action.channel,
              value: action.value,
            },
            state: {
              ...state,
              in0State: nextIn0State,
              xVal: action.value,
              state: isAllDone ? "writing_phase" : "reading_phase",
            },
          };
        }
        if (key === "in1" && last === "value" && state.in1State === "reading") {
          const nextIn1State = "done";
          const isAllDone =
            state.in0State === "done" && nextIn1State === "done";
          return {
            result: {
              kind: "read",
              channel: action.channel,
              value: action.value,
            },
            state: {
              ...state,
              in1State: nextIn1State,
              yVal: action.value,
              state: isAllDone ? "writing_phase" : "reading_phase",
            },
          };
        }
        return { result: { kind: "waiting" }, state };
      }

      // If no action, output copy writes
      if (state.in0State === "writing_copy") {
        return {
          result: { kind: "write", channel: ["in0", "copy"], value: null },
          state: {
            ...state,
            in0State: "reading",
          },
        };
      }
      if (state.in1State === "writing_copy") {
        return {
          result: { kind: "write", channel: ["in1", "copy"], value: null },
          state: {
            ...state,
            in1State: "reading",
          },
        };
      }
      return { result: { kind: "waiting" }, state };
    }

    if (state.state === "writing_phase") {
      return {
        result: {
          kind: "write",
          channel: ["out0", "set"],
          value: this.op(state.xVal, state.yVal),
        },
        state: {
          ...state,
          state: "done",
        },
      };
    }

    return { result: { kind: "done" }, state };
  }
}

export class AddCellMachine extends BinaryCellMachine {
  constructor() {
    super((x, y) => x + y);
  }
}

export const CharAtSpec = sequence(
  concurrent({
    in0: sequence(write(["copy"]), read(["value"])),
    in1: sequence(write(["copy"]), read(["value"])),
  }),
  write(["out0", "set"]),
);

export class CharAtMachine extends BinaryCellMachine {
  constructor() {
    super((str, index) => {
      if (typeof str !== "string") {
        throw new Error("First argument must be a string");
      }
      if (typeof index !== "number" || !Number.isInteger(index)) {
        throw new Error("Second argument must be an integer");
      }
      return str.charAt(index);
    });
  }
}

export class BinaryPredicateCellMachine implements MachineInstance {
  constructor(private pred: (x: any, y: any) => boolean) {}

  createState(): any {
    return {
      in0State: "writing_copy", // "writing_copy" | "reading" | "done"
      in1State: "writing_copy", // "writing_copy" | "reading" | "done"
      xVal: 0,
      yVal: 0,
      state: "reading_phase", // "reading_phase" | "writing_phase" | "done"
    };
  }

  getSpec(): MachineSpec {
    return sequence(
      concurrent({
        in0: sequence(write(["copy"]), read(["value"])),
        in1: sequence(write(["copy"]), read(["value"])),
      }),
      choice({
        true: write(["out0", "true"]),
        false: write(["out0", "false"]),
      }),
    );
  }

  isCompleted(state: any): boolean {
    return state.state === "done";
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "reading_phase") {
      if (action) {
        const key = action.channel[0];
        const last = action.channel[action.channel.length - 1];
        if (key === "in0" && last === "value" && state.in0State === "reading") {
          const nextIn0State = "done";
          const isAllDone =
            nextIn0State === "done" && state.in1State === "done";
          return {
            result: {
              kind: "read",
              channel: action.channel,
              value: action.value,
            },
            state: {
              ...state,
              in0State: nextIn0State,
              xVal: action.value,
              state: isAllDone ? "writing_phase" : "reading_phase",
            },
          };
        }
        if (key === "in1" && last === "value" && state.in1State === "reading") {
          const nextIn1State = "done";
          const isAllDone =
            state.in0State === "done" && nextIn1State === "done";
          return {
            result: {
              kind: "read",
              channel: action.channel,
              value: action.value,
            },
            state: {
              ...state,
              in1State: nextIn1State,
              yVal: action.value,
              state: isAllDone ? "writing_phase" : "reading_phase",
            },
          };
        }
        return { result: { kind: "waiting" }, state };
      }

      // If no action, output copy writes
      if (state.in0State === "writing_copy") {
        return {
          result: { kind: "write", channel: ["in0", "copy"], value: null },
          state: {
            ...state,
            in0State: "reading",
          },
        };
      }
      if (state.in1State === "writing_copy") {
        return {
          result: { kind: "write", channel: ["in1", "copy"], value: null },
          state: {
            ...state,
            in1State: "reading",
          },
        };
      }
      return { result: { kind: "waiting" }, state };
    }

    if (state.state === "writing_phase") {
      const outChan = this.pred(state.xVal, state.yVal)
        ? ["out0", "true"]
        : ["out0", "false"];
      return {
        result: { kind: "write", channel: outChan, value: null },
        state: {
          ...state,
          state: "done",
        },
      };
    }

    return { result: { kind: "done" }, state };
  }
}

export class LessThanCellMachine extends BinaryPredicateCellMachine {
  constructor() {
    super((x, y) => x < y);
  }
}

export class AreEqualCellMachine extends BinaryPredicateCellMachine {
  constructor() {
    super((x, y) => x === y);
  }
}

export const TestSpec = sequence(
  read(["input"]),
  choice({
    true: write(["out0", "true"]),
    false: write(["out0", "false"]),
  }),
);

export class TestMachine implements MachineInstance {
  createState(): any {
    return {
      inputVal: false,
      state: "reading",
    };
  }

  getSpec(): MachineSpec {
    return TestSpec;
  }

  isCompleted(state: any): boolean {
    return state.state === "done";
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "reading") {
      if (!action || !channelsEqual(action.channel, ["input"])) {
        return { result: { kind: "waiting" }, state };
      }
      return {
        result: { kind: "read", channel: ["input"], value: action.value },
        state: {
          ...state,
          inputVal: !!action.value,
          state: "writing",
        },
      };
    }

    if (state.state === "writing") {
      const outChan = state.inputVal ? ["out0", "true"] : ["out0", "false"];
      return {
        result: { kind: "write", channel: outChan, value: null },
        state: {
          ...state,
          state: "done",
        },
      };
    }

    return { result: { kind: "done" }, state };
  }
}

export function createIterSpec(spec: MachineSpec): MachineSpec {
  return sequence(
    loop(sequence(read(["next"]), write(["some"]), prefix(["value"], spec))),
    read(["next"]),
    write(["none"]),
  );
}

export const StringLengthSpec = UnaryCellSpec;

export class StringLengthMachine extends UnaryCellMachine {
  constructor() {
    super((val) => {
      if (typeof val !== "string") {
        throw new Error("Value is not a string");
      }
      return val.length;
    });
  }
}
