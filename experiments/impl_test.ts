import {
  MachineSpec,
  sequence,
  read,
  write,
  concurrent,
  choice,
  loop,
  complement,
  isCompleted,
  transition,
  indexed,
} from "./spec";
import {
  MachineInstance,
  StepResult,
  SequenceMachine,
  ConcurrentMachine,
  TraceMachine,
  WriteConstantMachine,
  DiscardMachine,
  LoopMachine,
  DupMachine,
  channelsEqual,
  RenameMachine,
  IndexedMachine,
} from "./impl";

class Runner {
  private state: any;
  constructor(private machine: MachineInstance) {
    this.state = machine.createState();
  }
  isCompleted(): boolean {
    return this.machine.isCompleted(this.state);
  }
  getSpec(): MachineSpec {
    return this.machine.getSpec();
  }
  step(action?: { channel: string[]; value?: any }): StepResult {
    const { result, state } = this.machine.step(this.state, action);
    this.state = state;
    return result;
  }
  getValue(): any {
    if ("getValue" in this.machine) {
      return (this.machine as any).getValue(this.state);
    }
    throw new Error("getValue not supported on this machine");
  }
  getState(): any {
    return this.state;
  }
}

class DoubleMachine implements MachineInstance {
  createState(): any {
    return {
      state: "init",
      val: 0,
    };
  }

  getSpec(): MachineSpec {
    return sequence(read(["a"]), write(["b"]));
  }

  isCompleted(state: any): boolean {
    return state.state === "done";
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "init") {
      return {
        result: { kind: "waiting" },
        state: {
          ...state,
          state: "waiting_a",
        },
      };
    }
    if (state.state === "waiting_a") {
      if (!action || action.channel[0] !== "a") {
        return { result: { kind: "waiting" }, state };
      }
      return {
        result: { kind: "read", channel: ["a"], value: action.value },
        state: {
          ...state,
          val: action.value,
          state: "ready_b",
        },
      };
    }
    if (state.state === "ready_b") {
      return {
        result: { kind: "write", channel: ["b"], value: state.val * 2 },
        state: {
          ...state,
          state: "done",
        },
      };
    }
    return { result: { kind: "done" }, state };
  }
}

class ProducerMachine implements MachineInstance {
  createState(): any {
    return {
      done: false,
    };
  }
  getSpec() {
    return write(["out"]);
  }
  isCompleted(state: any) {
    return state.done;
  }
  step(state: any): { result: StepResult; state: any } {
    if (state.done) return { result: { kind: "done" }, state };
    return {
      result: { kind: "write", channel: ["out"], value: 42 },
      state: {
        done: true,
      },
    };
  }
}

class ConsumerMachine implements MachineInstance {
  createState(): any {
    return {
      state: "waiting_in",
      val: 0,
    };
  }
  getSpec() {
    return sequence(read(["in"]), write(["result"]));
  }
  isCompleted(state: any) {
    return state.state === "done";
  }
  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "waiting_in") {
      if (!action || action.channel[0] !== "in")
        return { result: { kind: "waiting" }, state };
      return {
        result: { kind: "read", channel: ["in"], value: action.value },
        state: {
          ...state,
          val: action.value,
          state: "ready_res",
        },
      };
    }
    if (state.state === "ready_res") {
      return {
        result: { kind: "write", channel: ["result"], value: state.val * 2 },
        state: {
          ...state,
          state: "done",
        },
      };
    }
    return { result: { kind: "done" }, state };
  }
}

class PrefixProducer implements MachineInstance {
  createState(): any {
    return {
      done: false,
    };
  }
  getSpec() {
    return write(["mid", "data"]);
  }
  isCompleted(state: any) {
    return state.done;
  }
  step(state: any): { result: StepResult; state: any } {
    if (state.done) return { result: { kind: "done" }, state };
    return {
      result: { kind: "write", channel: ["mid", "data"], value: 100 },
      state: {
        done: true,
      },
    };
  }
}

class PrefixConsumer implements MachineInstance {
  createState(): any {
    return {
      state: "waiting_in",
      val: 0,
    };
  }
  getSpec() {
    return sequence(read(["mid", "data"]), write(["result"]));
  }
  isCompleted(state: any) {
    return state.state === "done";
  }
  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "waiting_in") {
      if (!action || !channelsEqual(action.channel, ["mid", "data"]))
        return { result: { kind: "waiting" }, state };
      return {
        result: { kind: "read", channel: ["mid", "data"], value: action.value },
        state: {
          ...state,
          val: action.value,
          state: "ready_res",
        },
      };
    }
    if (state.state === "ready_res") {
      return {
        result: { kind: "write", channel: ["result"], value: state.val * 3 },
        state: {
          ...state,
          state: "done",
        },
      };
    }
    return { result: { kind: "done" }, state };
  }
}

class ReadWriteMachine implements MachineInstance {
  createState(): any {
    return {
      val: undefined,
      state: "reading",
    };
  }
  getSpec(): MachineSpec {
    return sequence(read(["c"]), write(["d"]));
  }
  isCompleted(state: any): boolean {
    return state.state === "done";
  }
  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "reading") {
      if (!action || action.channel[0] !== "c")
        return { result: { kind: "waiting" }, state };
      return {
        result: { kind: "read", channel: ["c"], value: action.value },
        state: {
          ...state,
          val: action.value,
          state: "writing",
        },
      };
    }
    if (state.state === "writing") {
      return {
        result: { kind: "write", channel: ["d"], value: state.val },
        state: {
          ...state,
          state: "done",
        },
      };
    }
    return { result: { kind: "done" }, state };
  }
}

class ReadC implements MachineInstance {
  createState(): any {
    return {};
  }
  getSpec(): MachineSpec {
    return read(["c"]);
  }
  isCompleted(state: any): boolean {
    return false;
  }
  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (!action || action.channel[0] !== "c")
      return { result: { kind: "waiting" }, state };
    return {
      result: { kind: "read", channel: ["c"], value: action.value },
      state,
    };
  }
}

class PrefixedMachine implements MachineInstance {
  createState(): any {
    return { state: "reading" };
  }
  getSpec(): MachineSpec {
    return sequence(read(["c", "val"]), write(["c", "status"]));
  }
  isCompleted(state: any): boolean {
    return state.state === "done";
  }
  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "reading") {
      if (!action || !channelsEqual(action.channel, ["c", "val"]))
        return { result: { kind: "waiting" }, state };
      return {
        result: { kind: "read", channel: ["c", "val"], value: action.value },
        state: {
          ...state,
          state: "writing",
        },
      };
    }
    if (state.state === "writing") {
      return {
        result: { kind: "write", channel: ["c", "status"], value: "ok" },
        state: {
          ...state,
          state: "done",
        },
      };
    }
    return { result: { kind: "done" }, state };
  }
}

class MockWorker implements MachineInstance {
  createState(): any {
    return {
      done: false,
      val: undefined,
    };
  }
  getSpec(): MachineSpec {
    return sequence(read(["c"]), write(["d"]));
  }
  isCompleted(state: any): boolean {
    return state.done;
  }
  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (action) {
      return {
        result: { kind: "read", channel: ["c"], value: action.value },
        state: {
          ...state,
          val: action.value,
        },
      };
    }
    return {
      result: { kind: "write", channel: ["d"], value: state.val },
      state: {
        ...state,
        done: true,
      },
    };
  }
}

describe("step-by-step MachineInstance model", () => {
  it("drives a machine step-by-step", () => {
    const machine = new Runner(new DoubleMachine());
    expect(machine.isCompleted()).toBe(false);

    // 1. Initial state, returns waiting since first spec action is a read
    let res = machine.step();
    expect(res).toEqual({ kind: "waiting" });
    expect(machine.isCompleted()).toBe(false);

    // 2. Feed input for the read
    res = machine.step({ channel: ["a"], value: 10 });
    expect(res).toEqual({ kind: "read", channel: ["a"], value: 10 });
    expect(machine.isCompleted()).toBe(false);

    // 3. Step to execute the write
    res = machine.step();
    expect(res).toEqual({ kind: "write", channel: ["b"], value: 20 });
    expect(machine.isCompleted()).toBe(true);

    // 4. Step once more when done
    res = machine.step();
    expect(res).toEqual({ kind: "done" });
  });
});

describe("SequenceMachine", () => {
  it("runs machines sequentially", () => {
    const m1 = new DoubleMachine();
    const m2 = new DoubleMachine();
    const seq = new Runner(new SequenceMachine([m1, m2]));

    expect(seq.isCompleted()).toBe(false);

    // 1. Initial state of first machine
    expect(seq.step()).toEqual({ kind: "waiting" });

    // 2. Feed input to first machine
    expect(seq.step({ channel: ["a"], value: 5 })).toEqual({
      kind: "read",
      channel: ["a"],
      value: 5,
    });

    // 3. Let first machine write
    expect(seq.step()).toEqual({ kind: "write", channel: ["b"], value: 10 });
    // m1 is completed, but seq is not
    expect(seq.isCompleted()).toBe(false);

    // 4. Next step transitions from m1 (returning done) to m2 (returning waiting)
    expect(seq.step()).toEqual({ kind: "waiting" });

    // 5. Feed input to second machine
    expect(seq.step({ channel: ["a"], value: 8 })).toEqual({
      kind: "read",
      channel: ["a"],
      value: 8,
    });

    // 6. Let second machine write
    expect(seq.step()).toEqual({ kind: "write", channel: ["b"], value: 16 });
    // Both completed
    expect(seq.isCompleted()).toBe(true);

    // 7. Done
    expect(seq.step()).toEqual({ kind: "done" });
  });

  it("handles empty sequence", () => {
    const seq = new Runner(new SequenceMachine([]));
    expect(seq.isCompleted()).toBe(true);
    expect(seq.getSpec()).toEqual(sequence());
    expect(seq.step()).toEqual({ kind: "done" });
  });
});

describe("ConcurrentMachine", () => {
  it("runs machines concurrently", () => {
    const left = new DoubleMachine();
    const right = new DoubleMachine();
    const comp = new Runner(new ConcurrentMachine({ left, right }));

    expect(comp.isCompleted()).toBe(false);

    // 1. Initial state
    expect(comp.step()).toEqual({ kind: "waiting" });

    // 2. Interleave inputs
    expect(comp.step({ channel: ["left", "a"], value: 10 })).toEqual({
      kind: "read",
      channel: ["left", "a"],
      value: 10,
    });
    expect(comp.step({ channel: ["right", "a"], value: 30 })).toEqual({
      kind: "read",
      channel: ["right", "a"],
      value: 30,
    });

    // 3. Both are ready to write. Let's step one by one.
    expect(comp.step()).toEqual({
      kind: "write",
      channel: ["left", "b"],
      value: 20,
    });
    expect(comp.isCompleted()).toBe(false);

    expect(comp.step()).toEqual({
      kind: "write",
      channel: ["right", "b"],
      value: 60,
    });
    expect(comp.isCompleted()).toBe(true);

    // 4. Done
    expect(comp.step()).toEqual({ kind: "done" });
  });

  it("bypasses waiting machines to let advancing ones write", () => {
    const left = new DoubleMachine();
    const right = new DoubleMachine();
    const comp = new Runner(new ConcurrentMachine({ left, right }));

    // Initialize left into waiting state
    expect(comp.step()).toEqual({ kind: "waiting" });

    // Feed input to right only
    expect(comp.step({ channel: ["right", "a"], value: 50 })).toEqual({
      kind: "read",
      channel: ["right", "a"],
      value: 50,
    });

    // Now left is waiting, but right is ready to write.
    // Stepping without arguments should execute right's write.
    expect(comp.step()).toEqual({
      kind: "write",
      channel: ["right", "b"],
      value: 100,
    });

    // right is now completed, left is still waiting.
    expect(comp.isCompleted()).toBe(false);
    expect(comp.step()).toEqual({ kind: "waiting" });

    // Feed input to left to let it finish
    expect(comp.step({ channel: ["left", "a"], value: 5 })).toEqual({
      kind: "read",
      channel: ["left", "a"],
      value: 5,
    });
    expect(comp.step()).toEqual({
      kind: "write",
      channel: ["left", "b"],
      value: 10,
    });

    expect(comp.isCompleted()).toBe(true);
    expect(comp.step()).toEqual({ kind: "done" });
  });
});

describe("TraceMachine", () => {
  it("wires producer and consumer directly", () => {
    const producer = new ProducerMachine();
    const consumer = new ConsumerMachine();
    const comp = new ConcurrentMachine({ producer, consumer });

    // Wire producer's "out" to consumer's "in"
    const wired = new Runner(
      new TraceMachine(comp, ["producer", "out"], ["consumer", "in"]),
    );

    expect(wired.isCompleted()).toBe(false);

    // First step: producer writes "out", which is routed to consumer's "in" internally.
    // It keeps executing silently until it reaches the external write to "result".
    const res = wired.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["consumer", "result"],
      value: 84,
    });
    expect(wired.isCompleted()).toBe(true);

    // Done
    expect(wired.step()).toEqual({ kind: "done" });
  });

  it("wires producer and consumer via prefixes", () => {
    const producer = new ProducerMachine(); // writes ["out"], which is ["producer", "out"] under concurrent
    const consumer = new ConsumerMachine(); // reads ["in"], which is ["consumer", "in"] under concurrent
    const comp = new ConcurrentMachine({ producer, consumer });

    // Wire "producer" prefix directly to "consumer" prefix.
    // The write to ["producer", "out"] should map to ["consumer", "out"], which does NOT match the consumer's expected read of ["consumer", "in"]!
    const badWired = new Runner(
      new TraceMachine(comp, ["producer"], ["consumer"]),
    );
    expect(badWired.step()).toEqual({ kind: "waiting" });

    // Now, let's create a prefix-compatible pair:
    const prefProd = new PrefixProducer();
    const prefCons = new PrefixConsumer();
    const comp2 = new ConcurrentMachine({
      producer: prefProd,
      consumer: prefCons,
    });

    // Wire "producer.mid" prefix to "consumer.mid" prefix.
    // A write on ["producer", "mid", "data"] should map to ["consumer", "mid", "data"].
    // Since prefCons reads ["consumer", "mid", "data"], it should route successfully!
    const wired = new Runner(
      new TraceMachine(comp2, ["producer", "mid"], ["consumer", "mid"]),
    );
    expect(wired.isCompleted()).toBe(false);

    const res = wired.step();
    expect(res).toEqual({
      kind: "write",
      channel: ["consumer", "result"],
      value: 300,
    });
    expect(wired.isCompleted()).toBe(true);
  });
});

describe("WriteConstantMachine", () => {
  it("writes a static constant value and completes", () => {
    const m = new Runner(new WriteConstantMachine(["foo"], 42));
    expect(m.isCompleted()).toBe(false);
    expect(m.step()).toEqual({ kind: "write", channel: ["foo"], value: 42 });
    expect(m.isCompleted()).toBe(true);
    expect(m.step()).toEqual({ kind: "done" });
  });
});

describe("DiscardMachine", () => {
  it("reads a value, stores it, and completes", () => {
    const m = new Runner(new DiscardMachine(["foo"]));
    expect(m.isCompleted()).toBe(false);
    expect(m.step()).toEqual({ kind: "waiting" });
    expect(m.step({ channel: ["foo"], value: 100 })).toEqual({
      kind: "read",
      channel: ["foo"],
      value: 100,
    });
    expect(m.getValue()).toBe(100);
    expect(m.isCompleted()).toBe(true);
    expect(m.step()).toEqual({ kind: "done" });
  });
});

describe("LoopMachine", () => {
  it("runs an inner machine in a loop indefinitely", () => {
    let counter = 0;
    const m = new Runner(
      new LoopMachine(() => {
        counter++;
        return new WriteConstantMachine(["foo"], counter);
      }),
    );

    expect(m.isCompleted()).toBe(false);
    // Iteration 1
    expect(m.step()).toEqual({ kind: "write", channel: ["foo"], value: 1 });
    // Iteration 2
    expect(m.step()).toEqual({ kind: "write", channel: ["foo"], value: 2 });
    // Iteration 3
    expect(m.step()).toEqual({ kind: "write", channel: ["foo"], value: 3 });
    expect(m.isCompleted()).toBe(false);
  });
});

describe("DupMachine", () => {
  it("reads a value and copies it to multiple outputs concurrently", () => {
    const m = new Runner(new DupMachine(["in"], ["out1", "out2"]));
    expect(m.isCompleted()).toBe(false);
    expect(m.step()).toEqual({ kind: "waiting" });

    // Read input
    expect(m.step({ channel: ["in"], value: 99 })).toEqual({
      kind: "read",
      channel: ["in"],
      value: 99,
    });

    // Write outputs concurrently (order is determined by iteration over the object keys)
    const w1 = m.step();
    expect(w1.kind).toBe("write");
    if (w1.kind === "write") {
      expect(w1.value).toBe(99);
    }

    const w2 = m.step();
    expect(w2.kind).toBe("write");
    if (w2.kind === "write") {
      expect(w2.value).toBe(99);
    }

    if (w1.kind === "write" && w2.kind === "write") {
      expect(w1.channel).not.toEqual(w2.channel);
    }
    expect(m.isCompleted()).toBe(true);
  });
});

describe("RenameMachine", () => {
  it("renames read and write channels and produces the correct spec", () => {
    const inner = new ReadWriteMachine();
    const m = new Runner(
      new RenameMachine(inner, [
        [["c"], ["x"]],
        [["d"], ["y"]],
      ]),
    );

    // Verify spec matches
    expect(m.getSpec()).toEqual({
      kind: "rename",
      mapping: [
        [["c"], ["x"]],
        [["d"], ["y"]],
      ],
      inner: inner.getSpec(),
    });

    expect(m.isCompleted()).toBe(false);

    // Transition: external read "x"
    expect(m.step({ channel: ["x"], value: 42 })).toEqual({
      kind: "read",
      channel: ["x"],
      value: 42,
    });

    // Transition: external write "y"
    expect(m.step()).toEqual({
      kind: "write",
      channel: ["y"],
      value: 42,
    });

    expect(m.isCompleted()).toBe(true);
  });

  it("rejects transition attempts on internal mapped names", () => {
    const m = new Runner(new RenameMachine(new ReadC(), [[["c"], ["x"]]]));

    // Mapped external name works
    expect(m.step({ channel: ["x"], value: 1 })).toEqual({
      kind: "read",
      channel: ["x"],
      value: 1,
    });

    const m2 = new Runner(new RenameMachine(new ReadC(), [[["c"], ["x"]]]));
    // Original internal name is rejected
    expect(m2.step({ channel: ["c"], value: 1 })).toEqual({ kind: "waiting" });
  });

  it("supports prefix matching for multi-level paths", () => {
    const m = new Runner(
      new RenameMachine(new PrefixedMachine(), [[["c"], ["x"]]]),
    );

    // Read matches x.val -> c.val
    expect(m.step({ channel: ["x", "val"], value: 100 })).toEqual({
      kind: "read",
      channel: ["x", "val"],
      value: 100,
    });

    // Write outputs x.status -> c.status
    expect(m.step()).toEqual({
      kind: "write",
      channel: ["x", "status"],
      value: "ok",
    });
    expect(m.isCompleted()).toBe(true);
  });
});

describe("IndexedMachine", () => {
  it("instantiates family instances dynamically and routes steps correctly", () => {
    const m = new Runner(new IndexedMachine(() => new MockWorker()));

    // Spec matches template
    expect(m.getSpec()).toEqual({
      kind: "indexed",
      inner: sequence(read(["c"]), write(["d"])),
      active: {},
      activated: false,
      then: sequence(),
    });

    expect(m.isCompleted()).toBe(true);

    // Transition p0
    expect(m.step({ channel: ["p0", "c"], value: 100 })).toEqual({
      kind: "read",
      channel: ["p0", "c"],
      value: 100,
    });
    expect(m.isCompleted()).toBe(false);

    // Transition p1 concurrently
    expect(m.step({ channel: ["p1", "c"], value: 200 })).toEqual({
      kind: "read",
      channel: ["p1", "c"],
      value: 200,
    });

    // Step one of them (since they are in Record order, p0 is step first)
    expect(m.step()).toEqual({
      kind: "write",
      channel: ["p0", "d"],
      value: 100,
    });

    // Step the other one
    expect(m.step()).toEqual({
      kind: "write",
      channel: ["p1", "d"],
      value: 200,
    });

    expect(m.isCompleted()).toBe(true);
  });
});
