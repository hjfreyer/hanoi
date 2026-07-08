import { MachineSpec, build, sequence, read, write, concurrent, choice, loop, complement, isCompleted, transition } from "./spec";
import { MachineInstance, StepResult, SequenceMachine, ConcurrentMachine, TraceMachine, WriteConstantMachine, DiscardMachine, LoopMachine, DupMachine, channelsEqual, RenameMachine } from "./impl";

describe("step-by-step MachineInstance model", () => {
    class DoubleMachine implements MachineInstance {
        private spec: MachineSpec;
        private state: "init" | "waiting_a" | "ready_b" | "done" = "init";
        private val = 0;

        constructor() {
            this.spec = build(sequence(read(["a"]), write(["b"])));
        }

        getSpec(): MachineSpec {
            return this.spec;
        }

        isCompleted(): boolean {
            return isCompleted(this.spec);
        }

        step(action?: { channel: string[]; value?: any }): StepResult {
            if (this.state === "init") {
                this.state = "waiting_a";
                return { kind: "waiting" };
            }
            if (this.state === "waiting_a") {
                if (!action || action.channel[0] !== "a") {
                    return { kind: "waiting" };
                }
                this.val = action.value;
                const next = transition(this.spec, { kind: "read", channel: ["a"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.state = "ready_b";
                return { kind: "read", channel: ["a"], value: this.val };
            }
            if (this.state === "ready_b") {
                const next = transition(this.spec, { kind: "write", channel: ["b"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.state = "done";
                return { kind: "write", channel: ["b"], value: this.val * 2 };
            }
            return { kind: "done" };
        }
    }

    it("drives a machine step-by-step", () => {
        const machine = new DoubleMachine();
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
    class DoubleMachine implements MachineInstance {
        private spec: MachineSpec;
        private state: "init" | "waiting_a" | "ready_b" | "done" = "init";
        private val = 0;

        constructor() {
            this.spec = build(sequence(read(["a"]), write(["b"])));
        }

        getSpec(): MachineSpec {
            return this.spec;
        }

        isCompleted(): boolean {
            return isCompleted(this.spec);
        }

        step(action?: { channel: string[]; value?: any }): StepResult {
            if (this.state === "init") {
                this.state = "waiting_a";
                return { kind: "waiting" };
            }
            if (this.state === "waiting_a") {
                if (!action || action.channel[0] !== "a") {
                    return { kind: "waiting" };
                }
                this.val = action.value;
                const next = transition(this.spec, { kind: "read", channel: ["a"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.state = "ready_b";
                return { kind: "read", channel: ["a"], value: this.val };
            }
            if (this.state === "ready_b") {
                const next = transition(this.spec, { kind: "write", channel: ["b"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.state = "done";
                return { kind: "write", channel: ["b"], value: this.val * 2 };
            }
            return { kind: "done" };
        }
    }

    it("runs machines sequentially", () => {
        const m1 = new DoubleMachine();
        const m2 = new DoubleMachine();
        const seq = new SequenceMachine([m1, m2]);

        expect(seq.isCompleted()).toBe(false);

        // 1. Initial state of first machine
        expect(seq.step()).toEqual({ kind: "waiting" });

        // 2. Feed input to first machine
        expect(seq.step({ channel: ["a"], value: 5 })).toEqual({ kind: "read", channel: ["a"], value: 5 });

        // 3. Let first machine write
        expect(seq.step()).toEqual({ kind: "write", channel: ["b"], value: 10 });
        // m1 is completed, but seq is not
        expect(seq.isCompleted()).toBe(false);

        // 4. Next step transitions from m1 (returning done) to m2 (returning waiting)
        expect(seq.step()).toEqual({ kind: "waiting" });

        // 5. Feed input to second machine
        expect(seq.step({ channel: ["a"], value: 8 })).toEqual({ kind: "read", channel: ["a"], value: 8 });

        // 6. Let second machine write
        expect(seq.step()).toEqual({ kind: "write", channel: ["b"], value: 16 });
        // Both completed
        expect(seq.isCompleted()).toBe(true);

        // 7. Done
        expect(seq.step()).toEqual({ kind: "done" });
    });

    it("handles empty sequence", () => {
        const seq = new SequenceMachine([]);
        expect(seq.isCompleted()).toBe(true);
        expect(seq.getSpec()).toEqual({ kind: "done" });
        expect(seq.step()).toEqual({ kind: "done" });
    });
});

describe("ConcurrentMachine", () => {
    class DoubleMachine implements MachineInstance {
        private spec: MachineSpec;
        private state: "init" | "waiting_a" | "ready_b" | "done" = "init";
        private val = 0;

        constructor() {
            this.spec = build(sequence(read(["a"]), write(["b"])));
        }

        getSpec(): MachineSpec {
            return this.spec;
        }

        isCompleted(): boolean {
            return isCompleted(this.spec);
        }

        step(action?: { channel: string[]; value?: any }): StepResult {
            if (this.state === "init") {
                this.state = "waiting_a";
                return { kind: "waiting" };
            }
            if (this.state === "waiting_a") {
                if (!action || action.channel[0] !== "a") {
                    return { kind: "waiting" };
                }
                this.val = action.value;
                const next = transition(this.spec, { kind: "read", channel: ["a"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.state = "ready_b";
                return { kind: "read", channel: ["a"], value: this.val };
            }
            if (this.state === "ready_b") {
                const next = transition(this.spec, { kind: "write", channel: ["b"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.state = "done";
                return { kind: "write", channel: ["b"], value: this.val * 2 };
            }
            return { kind: "done" };
        }
    }

    it("runs machines concurrently", () => {
        const left = new DoubleMachine();
        const right = new DoubleMachine();
        const comp = new ConcurrentMachine({ left, right });

        expect(comp.isCompleted()).toBe(false);

        // 1. Initial state
        expect(comp.step()).toEqual({ kind: "waiting" });

        // 2. Interleave inputs
        expect(comp.step({ channel: ["left", "a"], value: 10 })).toEqual({ kind: "read", channel: ["left", "a"], value: 10 });
        expect(comp.step({ channel: ["right", "a"], value: 30 })).toEqual({ kind: "read", channel: ["right", "a"], value: 30 });

        // 3. Both are ready to write. Let's step one by one.
        expect(comp.step()).toEqual({ kind: "write", channel: ["left", "b"], value: 20 });
        expect(comp.isCompleted()).toBe(false);

        expect(comp.step()).toEqual({ kind: "write", channel: ["right", "b"], value: 60 });
        expect(comp.isCompleted()).toBe(true);

        // 4. Done
        expect(comp.step()).toEqual({ kind: "done" });
    });

    it("bypasses waiting machines to let advancing ones write", () => {
        const left = new DoubleMachine();
        const right = new DoubleMachine();
        const comp = new ConcurrentMachine({ left, right });

        // Initialize left into waiting state
        expect(comp.step()).toEqual({ kind: "waiting" });

        // Feed input to right only
        expect(comp.step({ channel: ["right", "a"], value: 50 })).toEqual({ kind: "read", channel: ["right", "a"], value: 50 });

        // Now left is waiting, but right is ready to write.
        // Stepping without arguments should execute right's write.
        expect(comp.step()).toEqual({ kind: "write", channel: ["right", "b"], value: 100 });

        // right is now completed, left is still waiting.
        expect(comp.isCompleted()).toBe(false);
        expect(comp.step()).toEqual({ kind: "waiting" });

        // Feed input to left to let it finish
        expect(comp.step({ channel: ["left", "a"], value: 5 })).toEqual({ kind: "read", channel: ["left", "a"], value: 5 });
        expect(comp.step()).toEqual({ kind: "write", channel: ["left", "b"], value: 10 });

        expect(comp.isCompleted()).toBe(true);
        expect(comp.step()).toEqual({ kind: "done" });
    });
});

describe("TraceMachine", () => {
    class ProducerMachine implements MachineInstance {
        private spec = build(write(["out"]));
        private done = false;
        getSpec() { return this.spec; }
        isCompleted() { return this.done; }
        step(): StepResult {
            if (this.done) return { kind: "done" };
            this.spec = { kind: "done" };
            this.done = true;
            return { kind: "write", channel: ["out"], value: 42 };
        }
    }

    class ConsumerMachine implements MachineInstance {
        private spec = build(sequence(read(["in"]), write(["result"])));
        private state: "waiting_in" | "ready_res" | "done" = "waiting_in";
        private val = 0;
        getSpec() { return this.spec; }
        isCompleted() { return this.state === "done"; }
        step(action?: { channel: string[]; value?: any }): StepResult {
            if (this.state === "waiting_in") {
                if (!action || action.channel[0] !== "in") return { kind: "waiting" };
                this.val = action.value;
                const next = transition(this.spec, { kind: "read", channel: ["in"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.state = "ready_res";
                return { kind: "read", channel: ["in"], value: this.val };
            }
            if (this.state === "ready_res") {
                const next = transition(this.spec, { kind: "write", channel: ["result"] });
                if (!next) throw new Error("Invalid transition");
                this.spec = next;
                this.state = "done";
                return { kind: "write", channel: ["result"], value: this.val * 2 };
            }
            return { kind: "done" };
        }
    }

    it("wires producer and consumer directly", () => {
        const producer = new ProducerMachine();
        const consumer = new ConsumerMachine();
        const comp = new ConcurrentMachine({ producer, consumer });
        
        // Wire producer's "out" to consumer's "in"
        const wired = new TraceMachine(comp, ["producer", "out"], ["consumer", "in"]);

        expect(wired.isCompleted()).toBe(false);

        // First step: producer writes "out", which is routed to consumer's "in" internally.
        // It keeps executing silently until it reaches the external write to "result".
        const res = wired.step();
        expect(res).toEqual({ kind: "write", channel: ["consumer", "result"], value: 84 });
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
        const badWired = new TraceMachine(comp, ["producer"], ["consumer"]);
        expect(badWired.step()).toEqual({ kind: "waiting" });

        // Now, let's create a prefix-compatible pair:
        class PrefixProducer implements MachineInstance {
            private spec = build(write(["mid", "data"]));
            private done = false;
            getSpec() { return this.spec; }
            isCompleted() { return this.done; }
            step(): StepResult {
                if (this.done) return { kind: "done" };
                this.spec = { kind: "done" };
                this.done = true;
                return { kind: "write", channel: ["mid", "data"], value: 100 };
            }
        }

        class PrefixConsumer implements MachineInstance {
            private spec = build(sequence(read(["mid", "data"]), write(["result"])));
            private state: "waiting_in" | "ready_res" | "done" = "waiting_in";
            private val = 0;
            getSpec() { return this.spec; }
            isCompleted() { return this.state === "done"; }
            step(action?: { channel: string[]; value?: any }): StepResult {
                if (this.state === "waiting_in") {
                    if (!action || !channelsEqual(action.channel, ["mid", "data"])) return { kind: "waiting" };
                    this.val = action.value;
                    const next = transition(this.spec, { kind: "read", channel: ["mid", "data"] });
                    if (!next) throw new Error("Invalid transition");
                    this.spec = next;
                    this.state = "ready_res";
                    return { kind: "read", channel: ["mid", "data"], value: this.val };
                }
                if (this.state === "ready_res") {
                    const next = transition(this.spec, { kind: "write", channel: ["result"] });
                    if (!next) throw new Error("Invalid transition");
                    this.spec = next;
                    this.state = "done";
                    return { kind: "write", channel: ["result"], value: this.val * 3 };
                }
                return { kind: "done" };
            }
        }

        const prefProd = new PrefixProducer();
        const prefCons = new PrefixConsumer();
        const comp2 = new ConcurrentMachine({ producer: prefProd, consumer: prefCons });

        // Wire "producer.mid" prefix to "consumer.mid" prefix.
        // A write on ["producer", "mid", "data"] should map to ["consumer", "mid", "data"].
        // Since prefCons reads ["consumer", "mid", "data"], it should route successfully!
        const wired = new TraceMachine(comp2, ["producer", "mid"], ["consumer", "mid"]);
        expect(wired.isCompleted()).toBe(false);

        const res = wired.step();
        expect(res).toEqual({ kind: "write", channel: ["consumer", "result"], value: 300 });
        expect(wired.isCompleted()).toBe(true);
    });
});

describe("WriteConstantMachine", () => {
    it("writes a static constant value and completes", () => {
        const m = new WriteConstantMachine(["foo"], 42);
        expect(m.isCompleted()).toBe(false);
        expect(m.step()).toEqual({ kind: "write", channel: ["foo"], value: 42 });
        expect(m.isCompleted()).toBe(true);
        expect(m.step()).toEqual({ kind: "done" });
    });
});

describe("DiscardMachine", () => {
    it("reads a value, stores it, and completes", () => {
        const m = new DiscardMachine(["foo"]);
        expect(m.isCompleted()).toBe(false);
        expect(m.step()).toEqual({ kind: "waiting" });
        expect(m.step({ channel: ["foo"], value: 100 })).toEqual({ kind: "read", channel: ["foo"], value: 100 });
        expect(m.getValue()).toBe(100);
        expect(m.isCompleted()).toBe(true);
        expect(m.step()).toEqual({ kind: "done" });
    });
});

describe("LoopMachine", () => {
    it("runs an inner machine in a loop indefinitely", () => {
        let counter = 0;
        const m = new LoopMachine(() => {
            counter++;
            return new WriteConstantMachine(["foo"], counter);
        });

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
        const m = new DupMachine(["in"], ["out1", "out2"]);
        expect(m.isCompleted()).toBe(false);
        expect(m.step()).toEqual({ kind: "waiting" });
        
        // Read input
        expect(m.step({ channel: ["in"], value: 99 })).toEqual({ kind: "read", channel: ["in"], value: 99 });
        
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
        // A machine that reads "c" and writes the read value to "d"
        class ReadWriteMachine implements MachineInstance {
            private val: any = undefined;
            private state: "reading" | "writing" | "done" = "reading";

            getSpec(): MachineSpec {
                return build(sequence(read(["c"]), write(["d"])));
            }
            isCompleted(): boolean {
                return this.state === "done";
            }
            step(action?: { channel: string[]; value?: any }): StepResult {
                if (this.state === "reading") {
                    if (!action || action.channel[0] !== "c") return { kind: "waiting" };
                    this.val = action.value;
                    this.state = "writing";
                    return { kind: "read", channel: ["c"], value: action.value };
                }
                if (this.state === "writing") {
                    this.state = "done";
                    return { kind: "write", channel: ["d"], value: this.val };
                }
                return { kind: "done" };
            }
        }

        const inner = new ReadWriteMachine();
        const m = new RenameMachine(inner, [ [["c"], ["x"]], [["d"], ["y"]] ]);

        // Verify spec matches
        expect(m.getSpec()).toEqual({
            kind: "rename",
            mapping: [ [["c"], ["x"]], [["d"], ["y"]] ],
            inner: inner.getSpec(),
            then: { kind: "done" }
        });

        expect(m.isCompleted()).toBe(false);

        // Transition: external read "x"
        expect(m.step({ channel: ["x"], value: 42 })).toEqual({
            kind: "read",
            channel: ["x"],
            value: 42
        });

        // Transition: external write "y"
        expect(m.step()).toEqual({
            kind: "write",
            channel: ["y"],
            value: 42
        });

        expect(m.isCompleted()).toBe(true);
    });

    it("rejects transition attempts on internal mapped names", () => {
        class ReadC implements MachineInstance {
            getSpec(): MachineSpec { return build(read(["c"])); }
            isCompleted(): boolean { return false; }
            step(action?: { channel: string[]; value?: any }): StepResult {
                if (!action || action.channel[0] !== "c") return { kind: "waiting" };
                return { kind: "read", channel: ["c"], value: action.value };
            }
        }

        const m = new RenameMachine(new ReadC(), [ [["c"], ["x"]] ]);

        // Mapped external name works
        expect(m.step({ channel: ["x"], value: 1 })).toEqual({ kind: "read", channel: ["x"], value: 1 });

        const m2 = new RenameMachine(new ReadC(), [ [["c"], ["x"]] ]);
        // Original internal name is rejected
        expect(m2.step({ channel: ["c"], value: 1 })).toEqual({ kind: "waiting" });
    });

    it("supports prefix matching for multi-level paths", () => {
        class PrefixedMachine implements MachineInstance {
            private state: "reading" | "writing" | "done" = "reading";
            getSpec(): MachineSpec { return build(sequence(read(["c", "val"]), write(["c", "status"]))); }
            isCompleted(): boolean { return this.state === "done"; }
            step(action?: { channel: string[]; value?: any }): StepResult {
                if (this.state === "reading") {
                    if (!action || !channelsEqual(action.channel, ["c", "val"])) return { kind: "waiting" };
                    this.state = "writing";
                    return { kind: "read", channel: ["c", "val"], value: action.value };
                }
                if (this.state === "writing") {
                    this.state = "done";
                    return { kind: "write", channel: ["c", "status"], value: "ok" };
                }
                return { kind: "done" };
            }
        }

        const m = new RenameMachine(new PrefixedMachine(), [ [["c"], ["x"]] ]);

        // Read matches x.val -> c.val
        expect(m.step({ channel: ["x", "val"], value: 100 })).toEqual({
            kind: "read",
            channel: ["x", "val"],
            value: 100
        });

        // Write outputs x.status -> c.status
        expect(m.step()).toEqual({
            kind: "write",
            channel: ["x", "status"],
            value: "ok"
        });
        expect(m.isCompleted()).toBe(true);
    });
});
