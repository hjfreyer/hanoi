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

export type MachineSpec = {
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
} | {
    kind: "trace"
    inner: MachineSpec
    pathA: string[]
    pathB: string[]
    then: MachineSpec
};

export type TranscriptEntry =  {
    kind: "read"
    channel: string[],
} | {
    kind: "write"
    channel: string[],
};

export type SpecBuilder = (next: MachineSpec) => MachineSpec;

function getSuffix(channel: string[], prefix: string[]): string[] | null {
    if (channel.length < prefix.length) return null;
    for (let i = 0; i < prefix.length; i++) {
        if (channel[i] !== prefix[i]) return null;
    }
    return channel.slice(prefix.length);
}

function resolveTraceInternal(inner: MachineSpec, pathA: string[], pathB: string[]): MachineSpec {
    let current = inner;
    while (true) {
        let transitioned = false;
        const possible = getPossibleTransitions(current);
        for (const ev of possible) {
            if (ev.kind === "write") {
                const suffixA = getSuffix(ev.channel, pathA);
                if (suffixA !== null) {
                    const mappedChannel = [...pathB, ...suffixA];
                    const next = transition(current, ev);
                    if (next) {
                        const next2 = transition(next, { kind: "read", channel: mappedChannel });
                        if (next2) {
                            current = next2;
                            transitioned = true;
                            break;
                        }
                    }
                }
                
                const suffixB = getSuffix(ev.channel, pathB);
                if (suffixB !== null) {
                    const mappedChannel = [...pathA, ...suffixB];
                    const next = transition(current, ev);
                    if (next) {
                        const next2 = transition(next, { kind: "read", channel: mappedChannel });
                        if (next2) {
                            current = next2;
                            transitioned = true;
                            break;
                        }
                    }
                }
            }
        }
        if (!transitioned) {
            break;
        }
    }
    return current;
}

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
    if (spec.kind === "trace") {
        const resolvedInner = resolveTraceInternal(spec.inner, spec.pathA, spec.pathB);
        const result: Array<{ kind: "read" | "write", channel: string[] }> = [];
        for (const ev of getFirstEvents(resolvedInner)) {
            if (getSuffix(ev.channel, spec.pathA) === null && getSuffix(ev.channel, spec.pathB) === null) {
                result.push(ev);
            }
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
    } else if (spec.kind === "trace") {
        validateSpec(spec.inner);
        validateSpec(spec.then);
    } else if (spec.kind === "read" || spec.kind === "write") {
        validateSpec(spec.then);
    }
}

export function build(builder: SpecBuilder): MachineSpec {
    const spec = builder({ kind: "done" });
    validateSpec(spec);
    return spec;
}

export function read(channel: string[]): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "read",
        channel,
        then: next
    });
}

export function write(channel: string[]): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "write",
        channel,
        then: next
    });
}

export function concurrent(machines: Record<string, MachineSpec>): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "concurrent",
        machines,
        then: next
    });
}

export function choice(choices: Record<string, MachineSpec>): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "choice",
        choices,
        then: next
    });
}

export function loop(body: MachineSpec): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "loop",
        body,
        then: next
    });
}

export function complement(inner: MachineSpec): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "complement",
        inner,
        then: next
    });
}

export function prefix(prefixPath: string[], inner: MachineSpec): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "prefix",
        prefix: prefixPath,
        inner,
        then: next
    });
}
export function trace(inner: MachineSpec, pathA: string[], pathB: string[]): SpecBuilder {
    return (next: MachineSpec) => ({
        kind: "trace",
        inner,
        pathA,
        pathB,
        then: next
    });
}

export function sequence(...parts: SpecBuilder[]): SpecBuilder {
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

export function isCompleted(spec: MachineSpec): boolean {
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
    if (spec.kind === "trace") {
        const resolvedInner = resolveTraceInternal(spec.inner, spec.pathA, spec.pathB);
        return isCompleted(resolvedInner) && isCompleted(spec.then);
    }
    return false;
}

export function transition(spec: MachineSpec, entry: TranscriptEntry): MachineSpec | null {
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

    if (spec.kind === "trace") {
        if (getSuffix(entry.channel, spec.pathA) !== null || getSuffix(entry.channel, spec.pathB) !== null) {
            return null;
        }

        const resolvedInner = resolveTraceInternal(spec.inner, spec.pathA, spec.pathB);
        const nextInner = transition(resolvedInner, entry);
        if (nextInner !== null) {
            const finalInner = resolveTraceInternal(nextInner, spec.pathA, spec.pathB);
            return {
                kind: "trace",
                inner: finalInner,
                pathA: spec.pathA,
                pathB: spec.pathB,
                then: spec.then
            };
        }

        if (isCompleted(resolvedInner)) {
            return transition(spec.then, entry);
        }
        return null;
    }

    return null;
}

export function getPossibleTransitions(spec: MachineSpec): TranscriptEntry[] {
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
    } else if (spec.kind === "trace") {
        const resolvedInner = resolveTraceInternal(spec.inner, spec.pathA, spec.pathB);
        for (const ev of getPossibleTransitions(resolvedInner)) {
            if (getSuffix(ev.channel, spec.pathA) === null && getSuffix(ev.channel, spec.pathB) === null) {
                result.push(ev);
            }
        }
        if (isCompleted(resolvedInner)) {
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

export type SubtypeResult = {
    isSubtype: true;
} | {
    isSubtype: false;
    reason: "completion" | "read" | "write";
    transcript: TranscriptEntry[];
};

export function isSubtype(a: MachineSpec, b: MachineSpec): SubtypeResult {
    const visited = new Set<string>();
    
    function check(currA: MachineSpec, currB: MachineSpec, path: TranscriptEntry[]): SubtypeResult {
        const stateKey = `${JSON.stringify(currA)}|${JSON.stringify(currB)}`;
        if (visited.has(stateKey)) {
            return { isSubtype: true };
        }
        visited.add(stateKey);
        
        if (isCompleted(currB) && !isCompleted(currA)) {
            return { isSubtype: false, reason: "completion", transcript: path };
        }
        
        const aTrans = getPossibleTransitions(currA);
        const bTrans = getPossibleTransitions(currB);
        
        // 1. Contravariant Inputs (Reads): every input that B accepts, A must also accept
        for (const t of bTrans) {
            if (t.kind === "read") {
                const nextA = transition(currA, t);
                if (nextA === null) {
                    return { isSubtype: false, reason: "read", transcript: [...path, t] };
                }
                const nextB = transition(currB, t)!;
                const result = check(nextA, nextB, [...path, t]);
                if (!result.isSubtype) {
                    return result;
                }
            }
        }
        
        // 2. Covariant Outputs (Writes): every output that A produces, B must also allow/expect
        for (const t of aTrans) {
            if (t.kind === "write") {
                const nextB = transition(currB, t);
                if (nextB === null) {
                    return { isSubtype: false, reason: "write", transcript: [...path, t] };
                }
                const nextA = transition(currA, t)!;
                const result = check(nextA, nextB, [...path, t]);
                if (!result.isSubtype) {
                    return result;
                }
            }
        }
        
        return { isSubtype: true };
    }
    
    return check(a, b, []);
}

export function checkTranscript(spec : MachineSpec, transcript: TranscriptEntry[]): boolean {
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

export function parseTranscript(text: string): TranscriptEntry[] {
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

export function hideSpecChannels(spec: MachineSpec, paths: string[][], prefix: string[] = []): MachineSpec {
    const isHidden = (channel: string[]) => {
        const absolute = [...prefix, ...channel];
        return paths.some(p => channelsEqual(absolute, p));
    };

    if (spec.kind === "read" || spec.kind === "write") {
        if (isHidden(spec.channel)) {
            return hideSpecChannels(spec.then, paths, prefix);
        }
        return {
            ...spec,
            then: hideSpecChannels(spec.then, paths, prefix)
        };
    }
    if (spec.kind === "done") {
        return spec;
    }
    if (spec.kind === "concurrent") {
        const sub: Record<string, MachineSpec> = {};
        for (const [key, m] of Object.entries(spec.machines)) {
            sub[key] = hideSpecChannels(m, paths, [...prefix, key]);
        }
        return {
            ...spec,
            machines: sub,
            then: hideSpecChannels(spec.then, paths, prefix)
        };
    }
    if (spec.kind === "choice") {
        const sub: Record<string, MachineSpec> = {};
        for (const [key, m] of Object.entries(spec.choices)) {
            sub[key] = hideSpecChannels(m, paths, prefix);
        }
        return {
            ...spec,
            choices: sub,
            then: hideSpecChannels(spec.then, paths, prefix),
            current: spec.current ? hideSpecChannels(spec.current, paths, prefix) : undefined
        };
    }
    if (spec.kind === "loop") {
        return {
            ...spec,
            body: hideSpecChannels(spec.body, paths, prefix),
            then: hideSpecChannels(spec.then, paths, prefix),
            current: spec.current ? hideSpecChannels(spec.current, paths, prefix) : undefined
        };
    }
    if (spec.kind === "prefix") {
        return {
            ...spec,
            inner: hideSpecChannels(spec.inner, paths, [...prefix, ...spec.prefix]),
            then: hideSpecChannels(spec.then, paths, prefix)
        };
    }
    if (spec.kind === "complement") {
        return {
            ...spec,
            inner: hideSpecChannels(spec.inner, paths, prefix),
            then: hideSpecChannels(spec.then, paths, prefix)
        };
    }
    return spec;
}
