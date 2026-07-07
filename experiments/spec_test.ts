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
 *    - Loop bodies are not complete while active. A loop is considered completed at iteration
 *      boundaries (where no iteration is in progress) if its continuation (`then`) is completed.
 *      To ensure deterministic execution without backtracking, specifications are statically
 *      validated at build-time to ensure that transition paths at choice points and loop
 *      boundaries are completely disjoint (LL(1) constraint).
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

function getFirstEvents(spec: MachineSpec): Array<{ kind: "read" | "write", channel: string[] }> {
    if (spec.kind === "read" || spec.kind === "write") {
        return [{ kind: spec.kind, channel: spec.channel }];
    }
    if (spec.kind === "choice") {
        const result: Array<{ kind: "read" | "write", channel: string[] }> = [];
        for (const branch of Object.values(spec.choices)) {
            result.push(...getFirstEvents(branch));
        }
        return result;
    }
    if (spec.kind === "loop") {
        return [...getFirstEvents(spec.body), ...getFirstEvents(spec.then)];
    }
    if (spec.kind === "concurrent") {
        const result: Array<{ kind: "read" | "write", channel: string[] }> = [];
        for (const [key, sub] of Object.entries(spec.machines)) {
            for (const ev of getFirstEvents(sub)) {
                result.push({ kind: ev.kind, channel: [key, ...ev.channel] });
            }
        }
        return result;
    }
    if (spec.kind === "prefix") {
        const result: Array<{ kind: "read" | "write", channel: string[] }> = [];
        for (const ev of getFirstEvents(spec.inner)) {
            result.push({ kind: ev.kind, channel: [...spec.prefix, ...ev.channel] });
        }
        return result;
    }
    if (spec.kind === "complement") {
        const result: Array<{ kind: "read" | "write", channel: string[] }> = [];
        for (const ev of getFirstEvents(spec.inner)) {
            result.push({ kind: ev.kind === "read" ? "write" : "read", channel: ev.channel });
        }
        return result;
    }
    return [];
}

function eventToString(ev: { kind: "read" | "write", channel: string[] }): string {
    return `${ev.kind}:${ev.channel.join(".")}`;
}

function validateSpec(spec: MachineSpec): void {
    if (spec.kind === "loop") {
        const bodyFirst = new Set(getFirstEvents(spec.body).map(eventToString));
        const thenFirst = new Set(getFirstEvents(spec.then).map(eventToString));
        
        for (const item of bodyFirst) {
            if (thenFirst.has(item)) {
                throw new Error(`Ambiguity detected in loop: both body and continuation can start with event "${item}"`);
            }
        }
        
        validateSpec(spec.body);
        validateSpec(spec.then);
    } else if (spec.kind === "choice") {
        const seen = new Set<string>();
        for (const branch of Object.values(spec.choices)) {
            const branchFirst = getFirstEvents(branch).map(eventToString);
            for (const item of branchFirst) {
                if (seen.has(item)) {
                    throw new Error(`Ambiguity detected in choice: multiple branches can start with event "${item}"`);
                }
                seen.add(item);
            }
            validateSpec(branch);
        }
        validateSpec(spec.then);
    } else if (spec.kind === "concurrent") {
        for (const child of Object.values(spec.machines)) {
            validateSpec(child);
        }
        validateSpec(spec.then);
    } else if (spec.kind === "prefix") {
        validateSpec(spec.inner);
        validateSpec(spec.then);
    } else if (spec.kind === "complement") {
        validateSpec(spec.inner);
        validateSpec(spec.then);
    } else if (spec.kind === "read" || spec.kind === "write") {
        validateSpec(spec.then);
    }
}

function build(builder: SpecBuilder): MachineSpec {
    const spec = builder({ kind: "done" });
    validateSpec(spec);
    return spec;
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
        return spec.current === undefined && isCompleted(spec.then);
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
        let nextSubSpec: MachineSpec | null = null;
        let matchedKey: string | null = null;
        
        if (entry.channel.length > 0) {
            const key = entry.channel[0];
            const subSpec = spec.machines[key];
            if (subSpec) {
                const strippedEntry: TranscriptEntry = {
                    kind: entry.kind,
                    channel: entry.channel.slice(1)
                };
                nextSubSpec = transition(subSpec, strippedEntry);
                if (nextSubSpec !== null) {
                    matchedKey = key;
                }
            }
        }
        
        if (nextSubSpec !== null && matchedKey !== null) {
            return {
                kind: "concurrent",
                machines: {
                    ...spec.machines,
                    [matchedKey]: nextSubSpec
                },
                then: spec.then
            };
        }
        
        const concurrentMachinesCompleted = Object.values(spec.machines).every(isCompleted);
        if (concurrentMachinesCompleted) {
            return transition(spec.then, entry);
        }
        
        return null;
    }

    if (spec.kind === "choice") {
        if (spec.selected === undefined) {
            let matchedKey: string | null = null;
            let nextSubSpec: MachineSpec | null = null;
            
            for (const [key, branch] of Object.entries(spec.choices)) {
                const next = transition(branch, entry);
                if (next !== null) {
                    if (matchedKey !== null) {
                        throw new Error(`Ambiguity detected in choice: multiple branches can transition on entry ${JSON.stringify(entry)}`);
                    }
                    matchedKey = key;
                    nextSubSpec = next;
                }
            }
            
            if (matchedKey === null || nextSubSpec === null) {
                return null;
            }
            
            return {
                kind: "choice",
                choices: spec.choices,
                then: spec.then,
                selected: matchedKey,
                current: nextSubSpec
            };
        } else {
            const nextSubSpec = transition(spec.current!, entry);
            if (nextSubSpec !== null) {
                return {
                    kind: "choice",
                    choices: spec.choices,
                    then: spec.then,
                    selected: spec.selected,
                    current: nextSubSpec
                };
            }
            if (isCompleted(spec.current!)) {
                return transition(spec.then, entry);
            }
            return null;
        }
    }

    if (spec.kind === "loop") {
        if (spec.current !== undefined) {
            const nextBody = transition(spec.current, entry);
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
        } else {
            const nextBody = transition(spec.body, entry);
            const nextThen = transition(spec.then, entry);
            
            if (nextBody !== null) {
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
            if (nextThen !== null) {
                return nextThen;
            }
            return null;
        }
    }

    if (spec.kind === "complement") {
        const reversedEntry: TranscriptEntry = {
            kind: entry.kind === "read" ? "write" : "read",
            channel: entry.channel
        };
        const nextInner = transition(spec.inner, reversedEntry);
        if (nextInner !== null) {
            return {
                kind: "complement",
                inner: nextInner,
                then: spec.then
            };
        }
        if (isCompleted(spec.inner)) {
            return transition(spec.then, entry);
        }
        return null;
    }

    if (spec.kind === "prefix") {
        if (entry.channel.length < spec.prefix.length) {
            if (isCompleted(spec.inner)) {
                return transition(spec.then, entry);
            }
            return null;
        }
        const hasPrefix = spec.prefix.every((val, index) => entry.channel[index] === val);
        let nextInner: MachineSpec | null = null;
        if (hasPrefix) {
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: entry.channel.slice(spec.prefix.length)
            };
            nextInner = transition(spec.inner, strippedEntry);
        }
        
        if (nextInner !== null) {
            return {
                kind: "prefix",
                prefix: spec.prefix,
                inner: nextInner,
                then: spec.then
            };
        }
        if (isCompleted(spec.inner)) {
            return transition(spec.then, entry);
        }
        return null;
    }

    return null;
}

function getPossibleTransitions(spec: MachineSpec): TranscriptEntry[] {
    const result: TranscriptEntry[] = [];
    
    if (spec.kind === "read" || spec.kind === "write") {
        result.push({ kind: spec.kind, channel: spec.channel });
    } else if (spec.kind === "choice") {
        if (spec.selected !== undefined) {
            result.push(...getPossibleTransitions(spec.current!));
        } else {
            for (const branch of Object.values(spec.choices)) {
                result.push(...getPossibleTransitions(branch));
            }
        }
    } else if (spec.kind === "loop") {
        if (spec.current !== undefined) {
            result.push(...getPossibleTransitions(spec.current));
        } else {
            result.push(...getPossibleTransitions(spec.body));
            result.push(...getPossibleTransitions(spec.then));
        }
    } else if (spec.kind === "concurrent") {
        for (const [key, sub] of Object.entries(spec.machines)) {
            for (const ev of getPossibleTransitions(sub)) {
                result.push({ kind: ev.kind, channel: [key, ...ev.channel] });
            }
        }
        const concurrentMachinesCompleted = Object.values(spec.machines).every(isCompleted);
        if (concurrentMachinesCompleted) {
            result.push(...getPossibleTransitions(spec.then));
        }
    } else if (spec.kind === "prefix") {
        for (const ev of getPossibleTransitions(spec.inner)) {
            result.push({ kind: ev.kind, channel: [...spec.prefix, ...ev.channel] });
        }
        if (isCompleted(spec.inner)) {
            result.push(...getPossibleTransitions(spec.then));
        }
    } else if (spec.kind === "complement") {
        for (const ev of getPossibleTransitions(spec.inner)) {
            result.push({ kind: ev.kind === "read" ? "write" : "read", channel: ev.channel });
        }
        if (isCompleted(spec.inner)) {
            result.push(...getPossibleTransitions(spec.then));
        }
    }
    
    // Deduplicate transitions
    const seen = new Set<string>();
    const uniqueResult: TranscriptEntry[] = [];
    for (const ev of result) {
        const key = `${ev.kind}:${ev.channel.join(".")}`;
        if (!seen.has(key)) {
            seen.add(key);
            uniqueResult.push(ev);
        }
    }
    
    return uniqueResult;
}

function isSubtype(a: MachineSpec, b: MachineSpec): boolean {
    const visited = new Set<string>();
    
    function check(currA: MachineSpec, currB: MachineSpec): boolean {
        const stateKey = `${JSON.stringify(currA)}|${JSON.stringify(currB)}`;
        if (visited.has(stateKey)) {
            return true;
        }
        visited.add(stateKey);
        
        if (isCompleted(currB) && !isCompleted(currA)) {
            return false;
        }
        
        const aTrans = getPossibleTransitions(currA);
        const bTrans = getPossibleTransitions(currB);
        
        // 1. Contravariant Inputs (Reads): every input that B accepts, A must also accept
        for (const t of bTrans) {
            if (t.kind === "read") {
                const nextA = transition(currA, t);
                if (nextA === null) {
                    return false;
                }
                const nextB = transition(currB, t)!;
                if (!check(nextA, nextB)) {
                    return false;
                }
            }
        }
        
        // 2. Covariant Outputs (Writes): every output that A produces, B must also allow/expect
        for (const t of aTrans) {
            if (t.kind === "write") {
                const nextB = transition(currB, t);
                if (nextB === null) {
                    return false;
                }
                const nextA = transition(currA, t)!;
                if (!check(nextA, nextB)) {
                    return false;
                }
            }
        }
        
        return true;
    }
    
    return check(a, b);
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
            < data
        `))).toBe(true);

        // branch 2
        expect(checkTranscript(spec, parseTranscript(`
            < msg
        `))).toBe(true);

        // invalid branch
        expect(checkTranscript(spec, parseTranscript(`
            < other
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
            < data
        `))).toBe(true);
    });

    it("fails if attempting to pass data to a completed choice branch", () => {
        const spec = build(choice({
            exit: { kind: "done" }
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < anything
        `))).toBe(false);
    });
});

describe("checkTranscript with loop", () => {
    it("matches a loop with 0 iterations", () => {
        const spec = build(loop(build(read(["foo"]))));
        expect(checkTranscript(spec, parseTranscript(``))).toBe(true);
    });

    it("matches a loop with multiple iterations", () => {
        const spec = build(loop(build(read(["foo"]))));
        expect(checkTranscript(spec, parseTranscript(`
            < foo
            < foo
            < foo
        `))).toBe(true);
    });

    it("fails if the loop body does not match", () => {
        const spec = build(loop(build(read(["foo"]))));
        expect(checkTranscript(spec, parseTranscript(`
            < bar
        `))).toBe(false);
    });

    it("fails when stopping in the middle of an iteration", () => {
        const spec = build(loop(build(sequence(read(["foo"]), write(["bar"])))));
        expect(checkTranscript(spec, parseTranscript(`
            < foo
        `))).toBe(false);
    });

    it("matches after a complete iteration", () => {
        const spec = build(loop(build(sequence(read(["foo"]), write(["bar"])))));
        expect(checkTranscript(spec, parseTranscript(`
            < foo
            > bar
        `))).toBe(true);
    });
});

describe("BorrowableSpec", () => {
    it("matches 0 iterations", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(``))).toBe(true);
    });

    it("matches 1 iteration", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < borrow
            > value
            < restore
        `))).toBe(true);
    });

    it("matches multiple iterations", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < borrow
            > value
            < restore
            < borrow
            > value
            < restore
        `))).toBe(true);
    });

    it("fails when stopping early in an iteration", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < borrow
            > value
        `))).toBe(false);
    });

    it("fails with incorrect kind for a step", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < borrow
            < value
            < restore
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
            < data
            < next
        `))).toBe(true);
    });

    it("matches loop with continuation", () => {
        const spec = build(sequence(
            loop(build(read(["foo"]))),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < foo
            < next
        `))).toBe(true);
    });

    it("does not require key prefix for choice branches anymore", () => {
        const spec = build(sequence(
            choice({
                ok: build(sequence(read(["data1"]), read(["data2"])))
            }),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < data1
            < data2
            < next
        `))).toBe(true);
    });
});

describe("pairBorrowableCopyable", () => {
    const spec = build(pairBorrowableCopyable);

    it("matches zero iterations of all component loops", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get
            > leftCmp.get
            < leftCmp.return
            > rightCmp.get
            < rightCmp.return
            > return
        `))).toBe(true);
    });

    it("matches with active iterations and nested loops", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get

            > leftCmp.get
            < leftCmp.left.borrow
            > left.left.borrow
            < left.left.value
            > leftCmp.left.value
            < leftCmp.left.restore
            > left.left.restore

            < leftCmp.right.borrow
            > right.left.borrow
            > leftCmp.right.value
            < right.left.value
            < leftCmp.right.restore
            > right.left.restore

            < leftCmp.right.borrow
            > right.left.borrow
            > leftCmp.right.value
            < right.left.value
            < leftCmp.right.restore
            > right.left.restore
            < leftCmp.return

            > rightCmp.get
            < rightCmp.return
            > return
        `))).toBe(true);
    });

    it("fails if attempting to transition sub-component before starting comparator", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get
            > leftCmp.left.borrow
        `))).toBe(false);
    });

    it("fails if loop iterations are incomplete", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get
            > left.left.borrow
            > leftCmp.get
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
            > foo
            < bar
            > foo
            < bar
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
            < a.b
            < a.b
            < next
        `))).toBe(true);
    });
});

describe("static validation (LL-1)", () => {
    it("throws error for ambiguous choice branches", () => {
        expect(() => {
            build(choice({
                branch1: build(read(["foo"])),
                branch2: build(read(["foo"]))
            }));
        }).toThrow(/Ambiguity detected in choice/);
    });

    it("throws error for ambiguous loop and continuation", () => {
        expect(() => {
            build(sequence(
                loop(build(read(["foo"]))),
                read(["foo"])
            ));
        }).toThrow(/Ambiguity detected in loop/);
    });

    it("allows non-overlapping choice branches", () => {
        expect(() => {
            build(choice({
                branch1: build(read(["foo"])),
                branch2: build(read(["bar"]))
            }));
        }).not.toThrow();
    });

    it("allows non-overlapping loop and continuation", () => {
        expect(() => {
            build(sequence(
                loop(build(read(["foo"]))),
                read(["bar"])
            ));
        }).not.toThrow();
    });
});

describe("isSubtype", () => {
    it("is reflexive (spec is subtype of itself)", () => {
        const spec = build(sequence(read(["foo"]), write(["bar"])));
        expect(isSubtype(spec, spec)).toBe(true);
        
        const loopSpec = BorrowableSpec;
        expect(isSubtype(loopSpec, loopSpec)).toBe(true);
    });

    it("supports contravariant inputs (reads)", () => {
        // A accepts more inputs than B. A is a subtype of B.
        const a = build(choice({
            ok: build(read(["data"])),
            err: build(read(["msg"]))
        }));
        const b = build(choice({
            ok: build(read(["data"]))
        }));
        expect(isSubtype(a, b)).toBe(true);
        expect(isSubtype(b, a)).toBe(false);
    });

    it("supports covariant outputs (writes)", () => {
        // A produces fewer outputs than B. A is a subtype of B.
        const a = build(choice({
            ok: build(write(["data"]))
        }));
        const b = build(choice({
            ok: build(write(["data"])),
            err: build(write(["msg"]))
        }));
        expect(isSubtype(a, b)).toBe(true);
        expect(isSubtype(b, a)).toBe(false);
    });

    it("respects completion constraints", () => {
        const a = build(read(["foo"]));
        const b = { kind: "done" } as MachineSpec;
        expect(isSubtype(a, b)).toBe(false);
        expect(isSubtype(b, a)).toBe(false);
        
        // done is a subtype of write(foo) because outputting nothing is a subset of outputting foo
        const c = build(write(["foo"]));
        expect(isSubtype(b, c)).toBe(true);
    });

    it("terminates and validates recursive specs (loops)", () => {
        const a = build(loop(build(read(["x"]))));
        const b = build(loop(build(read(["x"]))));
        expect(isSubtype(a, b)).toBe(true);
        
        const loopMore = build(loop(build(choice({
            x: build(read(["x"])),
            y: build(read(["y"]))
        }))));
        const loopLess = build(loop(build(read(["x"]))));
        expect(isSubtype(loopMore, loopLess)).toBe(true);
        expect(isSubtype(loopLess, loopMore)).toBe(false);
    });

    it("verifies sequential borrowable uses can subtype a single concurrent borrowable", () => {
        const workerA = build(complement(build(BorrowSpec)));
        const workerB = build(complement(build(BorrowSpec)));
        
        const subtype = build(sequence(
            concurrent({ worker: workerA, channel: BorrowableSpec }),
            concurrent({ worker: workerB, channel: BorrowableSpec })
        ));
        
        const supertype = build(concurrent({
            worker: build(sequence(complement(build(BorrowSpec)), complement(build(BorrowSpec)))),
            channel: BorrowableSpec
        }));
        
        expect(isSubtype(subtype, supertype)).toBe(true);
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