/**
 * Design Principles for Machine Specifications and Trace-Matching
 *
 * 1. Trace-Based Semantics (Transcript Matching)
 *    Specs define the set of allowed execution transcripts (sequences of reads '<' and writes '>')
 *    on channels. Rather than defining concrete code implementations, specs describe allowable
 *    interface behaviors.
 *
 * 2. Monotonic Completion (Liveness)
 *    Completion status is monotonic: once a machine reaches completion, it never transitions back
 *    to an incomplete state.
 *    - "Completed" is defined as: matching only the empty transcript.
 *    - Loop bodies and loops themselves are never complete while active. To exit a loop and reach
 *      completion, the loop must be explicitly exited via `break`, transitioning to its completed
 *      continuation (`then`).
 *
 * 3. Modular Continuations (Spec Builders)
 *    Sequential compositions and combinators are represented as functions (`SpecBuilder`) mapping
 *    the continuation (`then`) to the built spec. This eliminates intermediate linkage states and
 *    forces all sequences to be terminated explicitly.
 *
 * 4. Duality (Complement)
 *    A protocol spec (like a Borrowable channel spec) and the worker using that channel are duals.
 *    The `complement` combinator reverses the directions of reads and writes, allowing the same
 *    specification to be reused for both the provider and the client of a channel.
 *
 * 5. Isolation and Namespacing (Prefix)
 *    The `prefix` combinator namespaces all interactions of a sub-machine to a target channel path
 *    sequence, allowing modular composition of nested, concurrent components.
 */

type MachineSpec = {
    kind: "read"
    channel: string[],
    then: MachineSpec,
} | {
    kind: "write"
    channel: string[],
    then: MachineSpec,
} | {
    kind: "done"
} | {
    kind: "concurrent"
    machines: Record<string, MachineSpec>
    then: MachineSpec
} | {
    kind: "choice"
    choices: Record<string, MachineSpec>
    then: MachineSpec
    selected?: string
    current?: MachineSpec
} | {
    kind: "loop"
    body: MachineSpec
    then: MachineSpec
    current?: MachineSpec
} | {
    kind: "complement"
    inner: MachineSpec
    then: MachineSpec
} | {
    kind: "prefix"
    prefix: string[]
    inner: MachineSpec
    then: MachineSpec
};

type TranscriptEntry =  {
    kind: "read"
    channel: string[],
} | {
    kind: "write"
    channel: string[],
};

type SpecBuilder = (next: MachineSpec) => MachineSpec;

function build(builder: SpecBuilder): MachineSpec {
    return builder({ kind: "done" });
}

function read(channel: string[]): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "read",
        channel,
        then: next
    });
}

function write(channel: string[]): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "write",
        channel,
        then: next
    });
}

function concurrent(machines: Record<string, MachineSpec>): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "concurrent",
        machines,
        then: next
    });
}

function choice(choices: Record<string, MachineSpec>): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "choice",
        choices,
        then: next
    });
}

function loop(body: MachineSpec): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "loop",
        body,
        then: next
    });
}

function complement(inner: MachineSpec): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "complement",
        inner,
        then: next
    });
}

function prefix(prefixPath: string[], inner: MachineSpec): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "prefix",
        prefix: prefixPath,
        inner,
        then: next
    });
}

function sequence(...parts: SpecBuilder[]): SpecBuilder {
    return (next: MachineSpec) => {
        let spec = next;
        for (let i = parts.length - 1; i >= 0; i--) {
            spec = parts[i](spec);
        }
        return spec;
    };
}

function channelsEqual(a: string[], b: string[]): boolean {
    if (a.length !== b.length) return false;
    return a.every((val, index) => val === b[index]);
}

function isCompleted(spec: MachineSpec): boolean {
    if (spec.kind === "done") {
        return true;
    }
    if (spec.kind === "concurrent") {
        return Object.values(spec.machines).every(isCompleted) && isCompleted(spec.then);
    }
    if (spec.kind === "choice") {
        if (spec.selected === undefined) {
            return Object.values(spec.choices).some(isCompleted) && isCompleted(spec.then);
        } else {
            return isCompleted(spec.current!) && isCompleted(spec.then);
        }
    }
    if (spec.kind === "loop") {
        return false;
    }
    if (spec.kind === "complement") {
        return isCompleted(spec.inner) && isCompleted(spec.then);
    }
    if (spec.kind === "prefix") {
        return isCompleted(spec.inner) && isCompleted(spec.then);
    }
    return false;
}

function transition(spec: MachineSpec, entry: TranscriptEntry): MachineSpec | null {
    if (spec.kind === "done") {
        return null;
    }

    if (spec.kind === "read" || spec.kind === "write") {
        if (spec.kind === entry.kind && channelsEqual(spec.channel, entry.channel)) {
            return spec.then;
        }
        return null;
    }

    if (spec.kind === "concurrent") {
        const concurrentMachinesCompleted = Object.values(spec.machines).every(isCompleted);
        if (concurrentMachinesCompleted) {
            return transition(spec.then, entry);
        }
        if (entry.channel.length === 0) {
            return null;
        }
        const key = entry.channel[0];
        const subSpec = spec.machines[key];
        if (!subSpec) {
            return null;
        }
        const strippedEntry: TranscriptEntry = {
            kind: entry.kind,
            channel: entry.channel.slice(1)
        };
        const nextSubSpec = transition(subSpec, strippedEntry);
        if (nextSubSpec === null) {
            return null;
        }
        return {
            kind: "concurrent",
            machines: {
                ...spec.machines,
                [key]: nextSubSpec
            },
            then: spec.then
        };
    }

    if (spec.kind === "choice") {
        if (entry.channel.length === 0) {
            return null;
        }
        const key = entry.channel[0];
        
        if (spec.selected === undefined) {
            const subSpec = spec.choices[key];
            if (!subSpec) {
                return null;
            }
            if (isCompleted(subSpec)) {
                return null;
            }
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: entry.channel.slice(1)
            };
            const nextSubSpec = transition(subSpec, strippedEntry);
            if (nextSubSpec === null) {
                return null;
            }
            if (isCompleted(nextSubSpec)) {
                return spec.then;
            }
            return {
                kind: "choice",
                choices: spec.choices,
                then: spec.then,
                selected: key,
                current: nextSubSpec
            };
        } else {
            if (key !== spec.selected) {
                return null;
            }
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: entry.channel.slice(1)
            };
            const nextSubSpec = transition(spec.current!, strippedEntry);
            if (nextSubSpec === null) {
                return null;
            }
            if (isCompleted(nextSubSpec)) {
                return spec.then;
            }
            return {
                kind: "choice",
                choices: spec.choices,
                then: spec.then,
                selected: spec.selected,
                current: nextSubSpec
            };
        }
    }

    if (spec.kind === "loop") {
        if (entry.channel.length === 0) {
            return null;
        }
        const key = entry.channel[0];
        if (key === "step") {
            const activeBody = spec.current ?? spec.body;
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: entry.channel.slice(1)
            };
            const nextBody = transition(activeBody, strippedEntry);
            if (nextBody === null) {
                return null;
            }
            if (isCompleted(nextBody)) {
                return {
                    kind: "loop",
                    body: spec.body,
                    then: spec.then
                };
            }
            return {
                kind: "loop",
                body: spec.body,
                then: spec.then,
                current: nextBody
            };
        }
        if (key === "break") {
            const atBoundary = spec.current === undefined || isCompleted(spec.current);
            if (!atBoundary) {
                return null;
            }
            if (entry.channel.length !== 1) {
                return null;
            }
            return spec.then;
        }
        return null;
    }

    if (spec.kind === "complement") {
        const reversedEntry: TranscriptEntry = {
            kind: entry.kind === "read" ? "write" : "read",
            channel: entry.channel
        };
        const nextInner = transition(spec.inner, reversedEntry);
        if (nextInner === null) {
            return null;
        }
        if (isCompleted(nextInner)) {
            return spec.then;
        }
        return {
            kind: "complement",
            inner: nextInner,
            then: spec.then
        };
    }

    if (spec.kind === "prefix") {
        if (entry.channel.length < spec.prefix.length) {
            return null;
        }
        const hasPrefix = spec.prefix.every((val, index) => entry.channel[index] === val);
        if (!hasPrefix) {
            return null;
        }
        const strippedEntry: TranscriptEntry = {
            kind: entry.kind,
            channel: entry.channel.slice(spec.prefix.length)
        };
        const nextInner = transition(spec.inner, strippedEntry);
        if (nextInner === null) {
            return null;
        }
        if (isCompleted(nextInner)) {
            return spec.then;
        }
        return {
            kind: "prefix",
            prefix: spec.prefix,
            inner: nextInner,
            then: spec.then
        };
    }

    return null;
}

function checkTranscript(spec : MachineSpec, transcript: TranscriptEntry[]): boolean {
    let current = spec;
    for (const entry of transcript) {
        const next = transition(current, entry);
        if (next === null) {
            return false;
        }
        current = next;
    }
    return isCompleted(current);
}

function parseTranscript(text: string): TranscriptEntry[] {
    const lines = text.split(/\r?\n/);
    const result: TranscriptEntry[] = [];

    for (let line of lines) {
        line = line.trim();
        if (line === "") {
            continue;
        }

        const kindChar = line[0];
        if (kindChar !== "<" && kindChar !== ">") {
            throw new Error(`Invalid line format: must start with '<' or '>', got "${line}"`);
        }

        const kind = kindChar === "<" ? "read" : "write";
        const channelPart = line.slice(1).trim();
        if (channelPart === "") {
            throw new Error(`Invalid line format: missing channel name in "${line}"`);
        }

        const channel = channelPart.split(".").map(part => part.trim());
        if (channel.some(part => part === "")) {
            throw new Error(`Invalid channel path: contains empty segments in "${channelPart}"`);
        }

        result.push({ kind, channel });
    }

    return result;
}

const BorrowSpec : SpecBuilder = sequence(
    read(["borrow"]),
    write(["value"]),
    read(["restore"]),
);

const BorrowableSpec : MachineSpec = build(loop(build(BorrowSpec)));

const Copyable = build(loop(build(sequence(read(["copy"]), write(["value"])))));

function pairSpec(left : MachineSpec, right: MachineSpec): SpecBuilder {
    return concurrent({ left, right });
}

function comparator(inner : MachineSpec): SpecBuilder {
    return sequence(
        read(["get"]),
        pairSpec(build(complement(inner)), build(complement(inner))),
        write(["return"]),
    );
}

function pairComparator(left: MachineSpec, right: MachineSpec) {
    return sequence(
        read(["get"]),
        concurrent({
            left : build(complement(build(pairSpec(left, right)))),
            right : build(complement(build(pairSpec(left, right)))),
            leftCmp: build(complement(build(comparator(left)))),
            rightCmp: build(complement(build(comparator(right)))),
        }),
        write(["return"]),
    );
}

const pairBorrowableCopyable = pairComparator(BorrowableSpec, Copyable);

describe("sequence", () => {
    it("returns done for empty sequence", () => {
        expect(build(sequence())).toEqual({ kind: "done" });
    });

    it("creates nested MachineSpec for sequence of parts", () => {
        expect(build(sequence(
            read(["a"]),
            write(["b"])
        ))).toEqual({
            kind: "read",
            channel: ["a"],
            then: {
                kind: "write",
                channel: ["b"],
                then: { kind: "done" }
            }
        });
    });
});

describe("checkTranscript", () => {
    it("matches done with empty transcript", () => {
        expect(checkTranscript(build(sequence()), parseTranscript(``))).toBe(true);
    });

    it("does not match done with non-empty transcript", () => {
        expect(checkTranscript(build(sequence()), parseTranscript(`
            < a
        `))).toBe(false);
    });

    it("matches read with correct single entry", () => {
        expect(checkTranscript(build(sequence(read(["a", "b"]))), parseTranscript(`
            < a.b
        `))).toBe(true);
    });

    it("does not match read with wrong kind", () => {
        expect(checkTranscript(build(sequence(read(["a"]))), parseTranscript(`
            > a
        `))).toBe(false);
    });

    it("does not match read with wrong channel path", () => {
        expect(checkTranscript(build(sequence(read(["a", "b"]))), parseTranscript(`
            < a.c
        `))).toBe(false);
    });

    it("does not match read with different channel length", () => {
        expect(checkTranscript(build(sequence(read(["a"]))), parseTranscript(`
            < a.b
        `))).toBe(false);
    });

    it("does not match if transcript has multiple entries but spec ends with done", () => {
        expect(checkTranscript(
            build(sequence(read(["a"]))),
            parseTranscript(`
                < a
                < a
            `)
        )).toBe(false);
    });

    it("matches a multi-step sequence", () => {
        const spec = build(sequence(
            read(["a"]),
            write(["b"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < a
            > b
        `))).toBe(true);
    });

    it("does not match multi-step sequence with incorrect entry", () => {
        const spec = build(sequence(
            read(["a"]),
            write(["b"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < a
            < b
        `))).toBe(false);
    });
});

describe("checkTranscript with concurrent", () => {
    it("matches concurrent specs with interleaved entries", () => {
        const spec = build(concurrent({
            left: build(read(["foo"])),
            right: build(write(["bar"]))
        }));
        // interleaved 1
        expect(checkTranscript(spec, parseTranscript(`
            < left.foo
            > right.bar
        `))).toBe(true);

        // interleaved 2
        expect(checkTranscript(spec, parseTranscript(`
            > right.bar
            < left.foo
        `))).toBe(true);
    });

    it("does not match concurrent spec if one machine is not completed", () => {
        const spec = build(concurrent({
            left: build(read(["foo"])),
            right: build(write(["bar"]))
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < left.foo
        `))).toBe(false);
    });

    it("fails when passing data to a completed machine", () => {
        const spec = build(concurrent({
            left: build(read(["foo"])),
            right: build(write(["bar"]))
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < left.foo
            > right.bar
            < left.foo
        `))).toBe(false);
    });

    it("matches nested concurrent specs", () => {
        const spec = build(concurrent({
            outer: build(concurrent({
                inner: build(read(["foo"]))
            }))
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < outer.inner.foo
        `))).toBe(true);
    });
});

describe("checkTranscript with choice", () => {
    it("matches choice branches", () => {
        const spec = build(choice({
            ok: build(read(["data"])),
            err: build(read(["msg"]))
        }));
        // branch 1
        expect(checkTranscript(spec, parseTranscript(`
            < ok.data
        `))).toBe(true);

        // branch 2
        expect(checkTranscript(spec, parseTranscript(`
            < err.msg
        `))).toBe(true);

        // invalid branch
        expect(checkTranscript(spec, parseTranscript(`
            < other.data
        `))).toBe(false);
    });

    it("is completed if at least one branch is completed", () => {
        const spec = build(choice({
            ok: build(read(["data"])),
            exit: { kind: "done" }
        }));
        expect(checkTranscript(spec, parseTranscript(""))).toBe(true);
    });

    it("can still take a different branch even if one branch is completed", () => {
        const spec = build(choice({
            ok: build(read(["data"])),
            exit: { kind: "done" }
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < ok.data
        `))).toBe(true);
    });

    it("fails if attempting to pass data to a completed choice branch", () => {
        const spec = build(choice({
            exit: { kind: "done" }
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < exit.anything
        `))).toBe(false);
    });
});

describe("checkTranscript with loop", () => {
    it("matches a loop with 0 iterations", () => {
        const spec = build(loop(build(read(["foo"]))));
        expect(checkTranscript(spec, parseTranscript(`
            > break
        `))).toBe(true);
    });

    it("matches a loop with multiple iterations", () => {
        const spec = build(loop(build(read(["foo"]))));
        expect(checkTranscript(spec, parseTranscript(`
            < step.foo
            < step.foo
            < step.foo
            > break
        `))).toBe(true);
    });

    it("fails if the loop body does not match", () => {
        const spec = build(loop(build(read(["foo"]))));
        expect(checkTranscript(spec, parseTranscript(`
            < step.bar
        `))).toBe(false);
    });

    it("fails when breaking in the middle of an iteration", () => {
        const spec = build(loop(build(sequence(read(["foo"]), write(["bar"])))));
        expect(checkTranscript(spec, parseTranscript(`
            < step.foo
            > break
        `))).toBe(false);
    });

    it("matches after a complete iteration when breaking", () => {
        const spec = build(loop(build(sequence(read(["foo"]), write(["bar"])))));
        expect(checkTranscript(spec, parseTranscript(`
            < step.foo
            > step.bar
            > break
        `))).toBe(true);
    });
});

describe("BorrowableSpec", () => {
    it("matches 0 iterations", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            > break
        `))).toBe(true);
    });

    it("matches 1 iteration", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < step.borrow
            > step.value
            < step.restore
            > break
        `))).toBe(true);
    });

    it("matches multiple iterations", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < step.borrow
            > step.value
            < step.restore
            < step.borrow
            > step.value
            < step.restore
            > break
        `))).toBe(true);
    });

    it("fails when breaking early in an iteration", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < step.borrow
            > step.value
            > break
        `))).toBe(false);
    });

    it("fails with incorrect kind for a step", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < step.borrow
            < step.value
            < step.restore
            > break
        `))).toBe(false);
    });
});

describe("checkTranscript with continuations", () => {
    it("matches concurrent specs with interleaved entries and continuation", () => {
        const spec = build(sequence(
            concurrent({
                left: build(read(["foo"])),
                right: build(write(["bar"]))
            }),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < left.foo
            > right.bar
            < next
        `))).toBe(true);
    });

    it("matches choice specs with continuation", () => {
        const spec = build(sequence(
            choice({
                ok: build(read(["data"])),
                err: build(read(["msg"]))
            }),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < ok.data
            < next
        `))).toBe(true);
    });

    it("matches loop with continuation", () => {
        const spec = build(sequence(
            loop(build(read(["foo"]))),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < step.foo
            > break
            < next
        `))).toBe(true);
    });

    it("requires key prefix for subsequent steps in a selected choice branch", () => {
        const spec = build(sequence(
            choice({
                ok: build(sequence(read(["data1"]), read(["data2"])))
            }),
            read(["next"])
        ));
        // works with prefix on both steps
        expect(checkTranscript(spec, parseTranscript(`
            < ok.data1
            < ok.data2
            < next
        `))).toBe(true);

        // fails without prefix on the second step
        expect(checkTranscript(spec, parseTranscript(`
            < ok.data1
            < data2
            < next
        `))).toBe(false);
    });
});

describe("pairBorrowableCopyable", () => {
    const spec = build(pairBorrowableCopyable);

    it("matches zero iterations of all component loops", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get
            < left.left.break
            < left.right.break
            < right.left.break
            < right.right.break
            > leftCmp.get
            < leftCmp.left.break
            < leftCmp.right.break
            < leftCmp.return
            > rightCmp.get
            < rightCmp.left.break
            < rightCmp.right.break
            < rightCmp.return
            > return
        `))).toBe(true);
    });

    it("matches with active iterations and nested loops", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get

            > leftCmp.get
            < leftCmp.left.step.borrow
            > left.left.step.borrow
            < left.left.step.value
            > leftCmp.left.step.value
            < leftCmp.left.step.restore
            > left.left.step.restore
            > leftCmp.left.break
            < left.left.break

            < leftCmp.right.step.borrow
            > right.left.step.borrow
            > leftCmp.right.step.value
            < right.left.step.value
            < leftCmp.right.step.restore
            > right.left.step.restore

            < leftCmp.right.step.borrow
            > right.left.step.borrow
            > leftCmp.right.step.value
            < right.left.step.value
            < leftCmp.right.step.restore
            > right.left.step.restore
            > leftCmp.right.break
            < right.left.break

            > rightCmp.get
            > rightCmp.left.break
            < left.right.break
            > rightCmp.right.break
            < right.right.break

            < leftCmp.return
            < rightCmp.return
            > return
        `))).toBe(true);
    });

    it("fails if attempting to transition sub-component before starting comparator", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get
            > leftCmp.left.step.borrow
        `))).toBe(false);
    });

    it("fails if loop iterations are incomplete before breaking", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get
            > left.left.step.borrow
            < left.left.break
        `))).toBe(false);
    });
});

describe("checkTranscript with complement", () => {
    it("reverses reads and writes", () => {
        const spec = build(complement(build(sequence(
            read(["foo"]),
            write(["bar"])
        ))));
        // read becomes write, write becomes read
        expect(checkTranscript(spec, parseTranscript(`
            > foo
            < bar
        `))).toBe(true);

        // does not match if directions are not reversed
        expect(checkTranscript(spec, parseTranscript(`
            < foo
            > bar
        `))).toBe(false);
    });

    it("works with nested loops and continuations", () => {
        const spec = build(sequence(
            complement(build(loop(build(sequence(
                read(["foo"]),
                write(["bar"])
            ))))),
            read(["next"])
        ));
        // loop body: read(foo) -> write(bar).
        // Under complement: write(foo) -> read(bar).
        expect(checkTranscript(spec, parseTranscript(`
            > step.foo
            < step.bar
            > step.foo
            < step.bar
            > break
            < next
        `))).toBe(true);
    });
});

describe("checkTranscript with prefix", () => {
    it("prefixes read and write channels", () => {
        const spec = build(prefix(["a", "b"], build(sequence(
            read(["c"]),
            write(["d"])
        ))));
        expect(checkTranscript(spec, parseTranscript(`
            < a.b.c
            > a.b.d
        `))).toBe(true);

        // fails if prefix is incorrect
        expect(checkTranscript(spec, parseTranscript(`
            < c
            > d
        `))).toBe(false);
    });

    it("works with nested prefixing", () => {
        const spec = build(prefix(["a"], build(prefix(["b"], build(read(["c"]))))));
        expect(checkTranscript(spec, parseTranscript(`
            < a.b.c
        `))).toBe(true);
    });

    it("works with loops and continuations", () => {
        const spec = build(sequence(
            prefix(["a"], build(loop(build(read(["b"]))))),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < a.step.b
            < a.step.b
            > a.break
            < next
        `))).toBe(true);
    });
});

describe("parseTranscript", () => {
    it("parses read and write lines with period separators", () => {
        const text = `
            < foo.bar
            > baz.qux.quux
        `;
        expect(parseTranscript(text)).toEqual([
            { kind: "read", channel: ["foo", "bar"] },
            { kind: "write", channel: ["baz", "qux", "quux"] },
        ]);
    });

    it("handles trailing and leading whitespaces properly", () => {
        const text = "  <   a . b   \n  >  c  ";
        expect(parseTranscript(text)).toEqual([
            { kind: "read", channel: ["a", "b"] },
            { kind: "write", channel: ["c"] },
        ]);
    });

    it("ignores empty lines", () => {
        expect(parseTranscript("   \n\n  \n")).toEqual([]);
    });

    it("throws on invalid action prefix", () => {
        expect(() => parseTranscript("foo.bar")).toThrow();
        expect(() => parseTranscript("? foo.bar")).toThrow();
    });

    it("throws on missing channel name", () => {
        expect(() => parseTranscript("<")).toThrow();
        expect(() => parseTranscript(">   ")).toThrow();
    });

    it("throws on empty channel segments", () => {
        expect(() => parseTranscript("< foo..bar")).toThrow();
        expect(() => parseTranscript("< .")).toThrow();
    });
});