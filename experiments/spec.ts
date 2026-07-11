export type MachineSpec =
    | { kind: "read"; channel: string[] }
    | { kind: "write"; channel: string[] }
    | { kind: "sequence"; specs: MachineSpec[] }
    | { kind: "choice"; choices: MachineSpec[] }
    | { kind: "star"; inner: MachineSpec }
    | { kind: "concurrent"; machines: Record<string, MachineSpec> }
    | { kind: "complement"; inner: MachineSpec }
    | { kind: "rename"; mapping: Array<[string[], string[]]>; inner: MachineSpec }
    | { kind: "prefix"; prefix: string[]; inner: MachineSpec }
    | { kind: "indexed"; inner: MachineSpec; active: Record<string, MachineSpec>; activated: boolean; then: MachineSpec }
    | { kind: "trace"; inner: MachineSpec; pathA: string[]; pathB: string[] };

export type TranscriptEntry =
    | { kind: "read"; channel: string[] }
    | { kind: "write"; channel: string[] };

interface DfaTransition {
    kind: "read" | "write";
    channel: string[];
    targetIndex: number;
}

interface StandardDfaNode {
    kind?: "standard";
    index: number;
    isCompleted: boolean;
    transitions: DfaTransition[];
}

interface ConcurrentDfaNode {
    kind: "concurrent";
    index: number;
    machines: Record<string, number>;
    continuationIndex?: number;
}

interface ComplementDfaNode {
    kind: "complement";
    index: number;
    innerStartIndex: number;
}

interface RenameDfaNode {
    kind: "rename";
    index: number;
    innerStartIndex: number;
    mapping: Array<[string[], string[]]>;
}

interface PrefixDfaNode {
    kind: "prefix";
    index: number;
    innerStartIndex: number;
    prefix: string[];
}

interface IndexedDfaNode {
    kind: "indexed";
    index: number;
    innerStartIndex: number;
    continuationIndex?: number;
}

type DfaNode =
    | StandardDfaNode
    | ConcurrentDfaNode
    | ComplementDfaNode
    | RenameDfaNode
    | PrefixDfaNode
    | IndexedDfaNode;

export class DfaContext {
    nodes: DfaNode[] = [];
}

export interface CompiledSpec {
    context: DfaContext;
    startIndex: number;
}

type SubtypeResult =
    | { isSubtype: true }
    | { isSubtype: false; reason: "completion" | "read" | "write"; transcript: TranscriptEntry[] };

export type SpecBuilder = MachineSpec;

function channelsEqual(a: string[], b: string[]): boolean {
    if (a.length !== b.length) return false;
    return a.every((val, index) => val === b[index]);
}

function channelsMatch(pattern: string[], actual: string[]): boolean {
    if (pattern.length !== actual.length) return false;
    return pattern.every((val, index) => val === "*" || val === actual[index]);
}

function getSuffix(channel: string[], prefix: string[]): string[] | null {
    if (channel.length < prefix.length) return null;
    for (let i = 0; i < prefix.length; i++) {
        if (channel[i] !== prefix[i]) return null;
    }
    return channel.slice(prefix.length);
}

function translateOuterToInner(chan: string[], mapping: Array<[string[], string[]]>): string[] | null {
    for (const [from, to] of mapping) {
        if (getSuffix(chan, from) !== null && !channelsEqual(from, to)) {
            return null;
        }
    }
    for (const [from, to] of mapping) {
        const suffix = getSuffix(chan, to);
        if (suffix !== null) {
            return [...from, ...suffix];
        }
    }
    return chan;
}

function translateInnerToOuter(chan: string[], mapping: Array<[string[], string[]]>): string[] {
    for (const [from, to] of mapping) {
        const suffix = getSuffix(chan, from);
        if (suffix !== null) {
            return [...to, ...suffix];
        }
    }
    return chan;
}

function equals(a: MachineSpec, b: MachineSpec): boolean {
    if (a.kind !== b.kind) return false;
    switch (a.kind) {
        case "read":
            return channelsEqual(a.channel, (b as typeof a).channel);
        case "write":
            return channelsEqual(a.channel, (b as typeof a).channel);
        case "sequence":
            if (a.specs.length !== (b as typeof a).specs.length) return false;
            return a.specs.every((spec, i) => equals(spec, (b as typeof a).specs[i]));
        case "choice":
            if (a.choices.length !== (b as typeof a).choices.length) return false;
            return a.choices.every((choice, i) => equals(choice, (b as typeof a).choices[i]));
        case "star":
            return equals(a.inner, (b as typeof a).inner);
        case "concurrent": {
            const keysA = Object.keys(a.machines);
            const keysB = Object.keys((b as typeof a).machines);
            if (keysA.length !== keysB.length) return false;
            for (const key of keysA) {
                const subB = (b as typeof a).machines[key];
                if (!subB || !equals(a.machines[key], subB)) return false;
            }
            return true;
        }
        case "complement":
            return equals(a.inner, (b as typeof a).inner);
        case "rename": {
            if (a.mapping.length !== (b as typeof a).mapping.length) return false;
            for (let i = 0; i < a.mapping.length; i++) {
                const pairA = a.mapping[i];
                const pairB = (b as typeof a).mapping[i];
                if (!channelsEqual(pairA[0], pairB[0]) || !channelsEqual(pairA[1], pairB[1])) return false;
            }
            return equals(a.inner, (b as typeof a).inner);
        }
        case "prefix":
            return channelsEqual(a.prefix, (b as typeof a).prefix) && equals(a.inner, (b as typeof a).inner);
        case "indexed": {
            if (!equals(a.inner, (b as typeof a).inner)) return false;
            if (a.activated !== (b as typeof a).activated) return false;
            if (!equals(a.then, (b as typeof a).then)) return false;
            const keysA = Object.keys(a.active).sort();
            const keysB = Object.keys((b as typeof a).active).sort();
            if (keysA.length !== keysB.length) return false;
            for (let i = 0; i < keysA.length; i++) {
                if (keysA[i] !== keysB[i]) return false;
                if (!equals(a.active[keysA[i]], (b as typeof a).active[keysB[i]])) return false;
            }
            return true;
        }
        case "trace":
            return channelsEqual(a.pathA, (b as typeof a).pathA) &&
                   channelsEqual(a.pathB, (b as typeof a).pathB) &&
                   equals(a.inner, (b as typeof a).inner);
    }
}

export function read(channel: string[]): MachineSpec {
    return { kind: "read", channel };
}

export function write(channel: string[]): MachineSpec {
    return { kind: "write", channel };
}

export function sequence(...specs: MachineSpec[]): MachineSpec {
    const flat: MachineSpec[] = [];
    for (const spec of specs) {
        if (spec.kind === "sequence") {
            flat.push(...spec.specs);
        } else {
            flat.push(spec);
        }
    }

    // Link indexed continuations for completion semantics compatibility
    for (let i = 0; i < flat.length - 1; i++) {
        const spec = flat[i];
        if (spec.kind === "indexed") {
            const rest = sequence(...flat.slice(i + 1));
            (spec as any).then = rest;
        }
    }

    if (flat.length === 1) {
        return flat[0];
    }
    return { kind: "sequence", specs: flat };
}

export function choice(...args: any[]): MachineSpec {
    if (args.length === 1 && typeof args[0] === "object" && !Array.isArray(args[0]) && args[0] !== null && !("kind" in args[0])) {
        const record = args[0] as Record<string, MachineSpec>;
        return { kind: "choice", choices: Object.values(record) };
    }
    const flat: MachineSpec[] = [];
    for (const spec of args) {
        if (spec.kind === "choice") {
            flat.push(...spec.choices);
        } else {
            flat.push(spec);
        }
    }
    if (flat.length === 1) {
        return flat[0];
    }
    return { kind: "choice", choices: flat };
}

export function star(inner: MachineSpec): MachineSpec {
    return { kind: "star", inner };
}

export function loop(inner: MachineSpec): MachineSpec {
    return star(inner);
}

export function concurrent(machines: Record<string, MachineSpec>): MachineSpec {
    return { kind: "concurrent", machines };
}

export function complement(inner: MachineSpec): MachineSpec {
    if (inner.kind === "complement") {
        return inner.inner;
    }
    return { kind: "complement", inner };
}

export function rename(mapping: Array<[string[], string[]]>, inner: MachineSpec): MachineSpec {
    if (mapping.length === 0) {
        return inner;
    }
    return { kind: "rename", mapping, inner };
}

export function prefix(prefixPath: string[], inner: MachineSpec): MachineSpec {
    if (prefixPath.length === 0) {
        return inner;
    }
    if (inner.kind === "prefix") {
        return { kind: "prefix", prefix: [...prefixPath, ...inner.prefix], inner: inner.inner };
    }
    return { kind: "prefix", prefix: prefixPath, inner };
}

export function indexed(inner: MachineSpec, active: Record<string, MachineSpec> = {}): MachineSpec {
    return { kind: "indexed", inner, active, activated: false, then: sequence() };
}

export function trace(arg1: any, arg2: any, arg3?: any): MachineSpec {
    if (Array.isArray(arg1) && Array.isArray(arg2)) {
        return { kind: "trace", pathA: arg1, pathB: arg2, inner: arg3 };
    } else {
        return { kind: "trace", inner: arg1, pathA: arg2, pathB: arg3 };
    }
}

function validateSpec(spec: MachineSpec) {
    switch (spec.kind) {
        case "choice": {
            const seen = new Set<string>();
            for (const branch of spec.choices) {
                const possible = getPossibleTransitions(branch);
                for (const ev of possible) {
                    const key = `${ev.kind}:${ev.channel.join(".")}`;
                    if (seen.has(key)) {
                        throw new Error(`Ambiguity detected in choice: event ${ev.kind}(${ev.channel.join(".")}) accepted by multiple branches`);
                    }
                    seen.add(key);
                }
                validateSpec(branch);
            }
            break;
        }
        case "sequence": {
            for (let i = 0; i < spec.specs.length - 1; i++) {
                const current = spec.specs[i];
                if (current.kind === "star") {
                    const loopPoss = getPossibleTransitions(current.inner);
                    const contPoss = getPossibleTransitions(sequence(...spec.specs.slice(i + 1)));
                    for (const ev of loopPoss) {
                        const key = `${ev.kind}:${ev.channel.join(".")}`;
                        if (contPoss.some(c => `${c.kind}:${c.channel.join(".")}` === key)) {
                            throw new Error(`Ambiguity detected in loop: event ${ev.kind}(${ev.channel.join(".")}) accepted by both loop body and continuation`);
                        }
                    }
                }
            }
            for (const sub of spec.specs) {
                validateSpec(sub);
            }
            break;
        }
        case "star":
            validateSpec(spec.inner);
            break;
        case "concurrent":
            for (const sub of Object.values(spec.machines)) {
                validateSpec(sub);
            }
            break;
        case "complement":
        case "rename":
        case "prefix":
            validateSpec(spec.inner);
            break;
        case "indexed":
            validateSpec(spec.inner);
            for (const sub of Object.values(spec.active)) {
                validateSpec(sub);
            }
            break;
        case "trace":
            resolveEpsilonTransitions([spec.inner], spec.pathA, spec.pathB);
            validateSpec(spec.inner);
            break;
    }
}

export function build(spec: MachineSpec): MachineSpec {
    validateSpec(spec);
    return spec;
}

export function isCompleted(spec: MachineSpec): boolean {
    switch (spec.kind) {
        case "read":
        case "write":
            return false;
        case "sequence":
            return spec.specs.every(isCompleted);
        case "choice":
            return spec.choices.some(isCompleted);
        case "star":
            return true;
        case "concurrent":
            return Object.values(spec.machines).every(isCompleted);
        case "complement":
        case "rename":
        case "prefix":
            return isCompleted(spec.inner);
        case "indexed": {
            const allActiveCompleted = Object.values(spec.active).every(isCompleted);
            if (!allActiveCompleted) return false;
            if (spec.then.kind === "sequence" && spec.then.specs.length === 0) return true;
            return spec.activated ? isCompleted(spec.then) : false;
        }
        case "trace": {
            const closure = resolveEpsilonTransitions([spec.inner], spec.pathA, spec.pathB);
            return closure.some(isCompleted);
        }
    }
}

function transitionNfa(spec: MachineSpec, entry: TranscriptEntry): MachineSpec[] {
    switch (spec.kind) {
        case "read":
            if (entry.kind === "read" && channelsEqual(spec.channel, entry.channel)) {
                return [sequence()];
            }
            return [];
        case "write":
            if (entry.kind === "write" && channelsEqual(spec.channel, entry.channel)) {
                return [sequence()];
            }
            return [];
        case "choice": {
            const results: MachineSpec[] = [];
            for (const choiceSpec of spec.choices) {
                results.push(...transitionNfa(choiceSpec, entry));
            }
            return results;
        }
        case "sequence": {
            const results: MachineSpec[] = [];
            for (let i = 0; i < spec.specs.length; i++) {
                const head = spec.specs[i];
                const tail = spec.specs.slice(i + 1);

                const headTransitions = transitionNfa(head, entry);
                for (const nextHead of headTransitions) {
                    results.push(sequence(nextHead, ...tail));
                }

                if (!isCompleted(head)) {
                    break;
                }
            }
            return results;
        }
        case "star": {
            return transitionNfa(spec.inner, entry)
                .map(nextInner => sequence(nextInner, spec));
        }
        case "concurrent": {
            if (entry.channel.length === 0) return [];
            const key = entry.channel[0];
            const sub = spec.machines[key];
            if (!sub) return [];
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: entry.channel.slice(1)
            };
            return transitionNfa(sub, strippedEntry).map(nextSub => ({
                kind: "concurrent",
                machines: {
                    ...spec.machines,
                    [key]: nextSub
                }
            }));
        }
        case "complement": {
            const reversedEntry: TranscriptEntry = {
                kind: entry.kind === "read" ? "write" : "read",
                channel: entry.channel
            };
            return transitionNfa(spec.inner, reversedEntry).map(nextInner => complement(nextInner));
        }
        case "rename": {
            const innerChannel = translateOuterToInner(entry.channel, spec.mapping);
            if (innerChannel === null) return [];
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: innerChannel
            };
            return transitionNfa(spec.inner, strippedEntry).map(nextInner => rename(spec.mapping, nextInner));
        }
        case "prefix": {
            const suffix = getSuffix(entry.channel, spec.prefix);
            if (suffix === null) return [];
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: suffix
            };
            return transitionNfa(spec.inner, strippedEntry).map(nextInner => prefix(spec.prefix, nextInner));
        }
        case "indexed": {
            if (entry.channel.length === 0) return [];
            const index = entry.channel[0];
            const suffix = entry.channel.slice(1);
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: suffix
            };

            const results: MachineSpec[] = [];

            if (index.startsWith("*") && !spec.active[index]) {
                const starCount = Object.keys(spec.active).filter(k => k.startsWith("*")).length;
                if (starCount >= 3) {
                    return [];
                }
            }

            const subSpec = spec.active[index] || spec.inner;
            const nextSubs = transitionNfa(subSpec, strippedEntry);
            for (const nextSub of nextSubs) {
                const active = { ...spec.active };
                if (isCompleted(nextSub)) {
                    delete active[index];
                } else {
                    active[index] = nextSub;
                }
                results.push({
                    kind: "indexed",
                    inner: spec.inner,
                    active,
                    activated: true,
                    then: spec.then
                });
            }

            // Also allow transitioning the continuation if we are activated and all active are completed
            const allActiveCompleted = Object.values(spec.active).every(isCompleted);
            if (spec.activated && allActiveCompleted) {
                results.push(...transitionNfa(spec.then, entry));
            }

            return results;
        }
        case "trace": {
            if (getSuffix(entry.channel, spec.pathA) !== null || getSuffix(entry.channel, spec.pathB) !== null) {
                return [];
            }
            const closure = resolveEpsilonTransitions([spec.inner], spec.pathA, spec.pathB);
            const results: MachineSpec[] = [];
            for (const s of closure) {
                const nextStates = transitionNfa(s, entry);
                for (const nextState of nextStates) {
                    results.push(trace(spec.pathA, spec.pathB, nextState));
                }
            }
            return results;
        }
    }
}

export function transition(spec: MachineSpec, entry: TranscriptEntry): MachineSpec | null {
    const nexts = transitionNfa(spec, entry);
    return nexts.length > 0 ? nexts[0] : null;
}

export function getPossibleTransitions(spec: MachineSpec): TranscriptEntry[] {
    const result: TranscriptEntry[] = [];

    switch (spec.kind) {
        case "read":
        case "write":
            result.push({ kind: spec.kind, channel: spec.channel });
            break;
        case "choice":
            for (const sub of spec.choices) {
                result.push(...getPossibleTransitions(sub));
            }
            break;
        case "sequence":
            for (const sub of spec.specs) {
                result.push(...getPossibleTransitions(sub));
                if (!isCompleted(sub)) {
                    break;
                }
            }
            break;
        case "star":
            result.push(...getPossibleTransitions(spec.inner));
            break;
        case "concurrent":
            for (const [key, sub] of Object.entries(spec.machines)) {
                for (const t of getPossibleTransitions(sub)) {
                    result.push({ kind: t.kind, channel: [key, ...t.channel] });
                }
            }
            break;
        case "complement":
            for (const t of getPossibleTransitions(spec.inner)) {
                result.push({ kind: t.kind === "read" ? "write" : "read", channel: t.channel });
            }
            break;
        case "rename":
            for (const t of getPossibleTransitions(spec.inner)) {
                result.push({ kind: t.kind, channel: translateInnerToOuter(t.channel, spec.mapping) });
            }
            break;
        case "prefix":
            for (const t of getPossibleTransitions(spec.inner)) {
                result.push({ kind: t.kind, channel: [...spec.prefix, ...t.channel] });
            }
            break;
        case "indexed":
            for (const [key, subSpec] of Object.entries(spec.active)) {
                for (const t of getPossibleTransitions(subSpec)) {
                    result.push({ kind: t.kind, channel: [key, ...t.channel] });
                }
            }
            let nextKeyIdx = 0;
            while (spec.active[`*${nextKeyIdx}`]) {
                nextKeyIdx++;
            }
            const nextKey = `*${nextKeyIdx}`;
            for (const t of getPossibleTransitions(spec.inner)) {
                result.push({ kind: t.kind, channel: [nextKey, ...t.channel] });
            }
            // If activated and all active are completed, we can also transition the continuation
            const allActiveCompleted = Object.values(spec.active).every(isCompleted);
            if (spec.activated && allActiveCompleted) {
                result.push(...getPossibleTransitions(spec.then));
            }
            break;
        case "trace": {
            const closure = resolveEpsilonTransitions([spec.inner], spec.pathA, spec.pathB);
            for (const s of closure) {
                for (const t of getPossibleTransitions(s)) {
                    if (getSuffix(t.channel, spec.pathA) === null && getSuffix(t.channel, spec.pathB) === null) {
                        result.push(t);
                    }
                }
            }
            break;
        }
    }

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


function deduplicateStates(states: MachineSpec[]): MachineSpec[] {
    const result: MachineSpec[] = [];
    for (const state of states) {
        if (!result.some(r => equals(r, state))) {
            result.push(state);
        }
    }
    return result;
}

function stateSetsEqual(a: MachineSpec[], b: MachineSpec[]): boolean {
    if (a.length !== b.length) return false;
    return a.every(x => b.some(y => equals(x, y)));
}

function resolveEpsilonTransitions(states: MachineSpec[], pathA: string[], pathB: string[]): MachineSpec[] {
    const closure = deduplicateStates(states);
    const queue = [...closure];

    while (queue.length > 0) {
        const current = queue.shift()!;
        const possible = getPossibleTransitions(current);

        for (const ev of possible) {
            if (ev.kind === "write") {
                const suffixA = getSuffix(ev.channel, pathA);
                if (suffixA !== null) {
                    const readChannel = [...pathB, ...suffixA];
                    const readEvent: TranscriptEntry = { kind: "read", channel: readChannel };

                    const intermediateStates = transitionNfa(current, ev);
                    if (intermediateStates.length > 0) {
                        let matched = false;
                        for (const s1 of intermediateStates) {
                            const nextStates = transitionNfa(s1, readEvent);
                            if (nextStates.length > 0) {
                                matched = true;
                                for (const s2 of nextStates) {
                                    if (!closure.some(c => equals(c, s2))) {
                                        closure.push(s2);
                                        queue.push(s2);
                                    }
                                }
                            }
                        }
                        if (!matched) {
                            throw new Error(`Blocked wired transition: ${ev.channel.join(".")} has no matching reader`);
                        }
                    }
                }

                const suffixB = getSuffix(ev.channel, pathB);
                if (suffixB !== null) {
                    const readChannel = [...pathA, ...suffixB];
                    const readEvent: TranscriptEntry = { kind: "read", channel: readChannel };

                    const intermediateStates = transitionNfa(current, ev);
                    if (intermediateStates.length > 0) {
                        let matched = false;
                        for (const s1 of intermediateStates) {
                            const nextStates = transitionNfa(s1, readEvent);
                            if (nextStates.length > 0) {
                                matched = true;
                                for (const s2 of nextStates) {
                                    if (!closure.some(c => equals(c, s2))) {
                                        closure.push(s2);
                                        queue.push(s2);
                                    }
                                }
                            }
                        }
                        if (!matched) {
                            throw new Error(`Blocked wired transition: ${ev.channel.join(".")} has no matching reader`);
                        }
                    }
                }
            }
        }
    }
    return closure;
}

function hasConcurrent(spec: MachineSpec): boolean {
    switch (spec.kind) {
        case "concurrent":
            return true;
        case "sequence":
            return spec.specs.some(hasConcurrent);
        case "choice":
            return spec.choices.some(hasConcurrent);
        case "star":
        case "complement":
        case "rename":
        case "prefix":
            return hasConcurrent(spec.inner);
        case "indexed":
            return true;
        case "trace":
            return hasConcurrent(spec.inner);
        default:
            return false;
    }
}

function compileStructural(spec: MachineSpec, context: DfaContext): number | null {
    if (!hasConcurrent(spec)) return null;

    if (spec.kind === "concurrent") {
        const subIndices: Record<string, number> = {};
        for (const [key, subSpec] of Object.entries(spec.machines)) {
            subIndices[key] = compile(subSpec, context);
        }
        const index = context.nodes.length;
        context.nodes.push({
            kind: "concurrent",
            index,
            machines: subIndices
        });
        return index;
    }
    if (spec.kind === "indexed") {
        const innerStart = compile(spec.inner, context);
        const index = context.nodes.length;
        context.nodes.push({
            kind: "indexed",
            index,
            innerStartIndex: innerStart
        });
        return index;
    }
    if (spec.kind === "complement") {
        const innerStart = compile(spec.inner, context);
        const index = context.nodes.length;
        context.nodes.push({
            kind: "complement",
            index,
            innerStartIndex: innerStart
        });
        return index;
    }
    if (spec.kind === "rename") {
        const innerStart = compile(spec.inner, context);
        const index = context.nodes.length;
        context.nodes.push({
            kind: "rename",
            index,
            innerStartIndex: innerStart,
            mapping: spec.mapping
        });
        return index;
    }
    if (spec.kind === "prefix") {
        const innerStart = compile(spec.inner, context);
        const index = context.nodes.length;
        context.nodes.push({
            kind: "prefix",
            index,
            innerStartIndex: innerStart,
            prefix: spec.prefix
        });
        return index;
    }
    if (spec.kind === "sequence" && spec.specs.length > 0) {
        const head = spec.specs[0];
        const tail = spec.specs.slice(1);
        
        const headIdx = compileStructural(head, context);
        if (headIdx !== null) {
            const tailIndex = compile(sequence(...tail), context);
            const headNode = context.nodes[headIdx];
            if (headNode.kind === "concurrent" || headNode.kind === "indexed") {
                headNode.continuationIndex = tailIndex;
            } else if (headNode.kind === "complement" || headNode.kind === "rename" || headNode.kind === "prefix") {
                let current: any = headNode;
                while (current.kind === "complement" || current.kind === "rename" || current.kind === "prefix") {
                    current = context.nodes[current.innerStartIndex];
                }
                if (current.kind === "concurrent" || current.kind === "indexed") {
                    current.continuationIndex = tailIndex;
                }
            }
            return headIdx;
        }
    }
    return null;
}

function compile(spec: MachineSpec, context: DfaContext): number {
    const structIndex = compileStructural(spec, context);
    if (structIndex !== null) return structIndex;

    const nodeStates: MachineSpec[][] = [];
    const startOffset = context.nodes.length;

    function getOrCreateNodeIndex(states: MachineSpec[]): number {
        for (let i = 0; i < nodeStates.length; i++) {
            if (stateSetsEqual(nodeStates[i], states)) {
                return startOffset + i;
            }
        }
        const index = startOffset + nodeStates.length;
        nodeStates.push(states);
        context.nodes.push({
            index,
            isCompleted: states.some(isCompleted),
            transitions: []
        });
        return index;
    }

    const initialStates = deduplicateStates([spec]);
    const startIndex = getOrCreateNodeIndex(initialStates);

    let processedCount = 0;
    while (processedCount < nodeStates.length) {
        const localIndex = processedCount;
        processedCount++;

        const currentNfaStates = nodeStates[localIndex];
        const node = context.nodes[startOffset + localIndex] as StandardDfaNode;

        const possibleEvents: TranscriptEntry[] = [];
        for (const s of currentNfaStates) {
            possibleEvents.push(...getPossibleTransitions(s));
        }

        const seenEvents = new Set<string>();
        const uniqueEvents: TranscriptEntry[] = [];
        for (const ev of possibleEvents) {
            const evKey = `${ev.kind}:${ev.channel.join(".")}`;
            if (!seenEvents.has(evKey)) {
                seenEvents.add(evKey);
                uniqueEvents.push(ev);
            }
        }

        for (const entry of uniqueEvents) {
            const nextStatesRaw: MachineSpec[] = [];
            for (const s of currentNfaStates) {
                nextStatesRaw.push(...transitionNfa(s, entry));
            }
            const nextStates = deduplicateStates(nextStatesRaw);
            if (nextStates.length > 0) {
                let targetIndex: number;
                let structIdx: number | null = null;
                if (nextStates.length === 1) {
                    structIdx = compileStructural(nextStates[0], context);
                }
                if (structIdx !== null) {
                    targetIndex = structIdx;
                } else {
                    targetIndex = getOrCreateNodeIndex(nextStates);
                }
                node.transitions.push({
                    kind: entry.kind,
                    channel: entry.channel,
                    targetIndex
                });
            }
        }
    }

    return startIndex;
}

export function compileToSpec(spec: MachineSpec): CompiledSpec {
    const context = new DfaContext();
    const startIndex = compile(spec, context);
    return { context, startIndex };
}

type DfaRunState =
    | { kind: "standard"; index: number }
    | { kind: "concurrent"; index: number; machines: Record<string, DfaRunState> }
    | { kind: "complement"; inner: DfaRunState }
    | { kind: "rename"; inner: DfaRunState; mapping: Array<[string[], string[]]> }
    | { kind: "prefix"; inner: DfaRunState; prefix: string[] }
    | { kind: "indexed"; index: number; active: Record<string, DfaRunState>; activated: boolean };

function initRunState(index: number, context: DfaContext): DfaRunState {
    const node = context.nodes[index];
    if (node.kind === "concurrent") {
        const machines: Record<string, DfaRunState> = {};
        for (const [key, subStart] of Object.entries(node.machines)) {
            machines[key] = initRunState(subStart, context);
        }
        return { kind: "concurrent", index, machines };
    }
    if (node.kind === "indexed") {
        return { kind: "indexed", index, active: {}, activated: false };
    }
    if (node.kind === "complement") {
        return { kind: "complement", inner: initRunState(node.innerStartIndex, context) };
    }
    if (node.kind === "rename") {
        return { kind: "rename", inner: initRunState(node.innerStartIndex, context), mapping: node.mapping };
    }
    if (node.kind === "prefix") {
        return { kind: "prefix", inner: initRunState(node.innerStartIndex, context), prefix: node.prefix };
    }
    return { kind: "standard", index };
}

function isRunStateCompleted(state: DfaRunState, context: DfaContext): boolean {
    if (state.kind === "concurrent") {
        const node = context.nodes[state.index] as ConcurrentDfaNode;
        const allSubCompleted = Object.values(state.machines).every(s => isRunStateCompleted(s, context));
        if (allSubCompleted) {
            if (node.continuationIndex !== undefined) {
                return isRunStateCompleted(initRunState(node.continuationIndex, context), context);
            }
            return true;
        }
        return false;
    }
    if (state.kind === "indexed") {
        const node = context.nodes[state.index] as IndexedDfaNode;
        const allActiveCompleted = Object.values(state.active).every(s => isRunStateCompleted(s, context));
        if (!allActiveCompleted) return false;
        if (node.continuationIndex !== undefined) {
            return state.activated ? isRunStateCompleted(initRunState(node.continuationIndex, context), context) : false;
        }
        return true;
    }
    if (state.kind === "complement") {
        return isRunStateCompleted(state.inner, context);
    }
    if (state.kind === "rename") {
        return isRunStateCompleted(state.inner, context);
    }
    if (state.kind === "prefix") {
        return isRunStateCompleted(state.inner, context);
    }
    const node = context.nodes[state.index] as StandardDfaNode;
    return node.isCompleted;
}

function transitionRunState(state: DfaRunState, entry: TranscriptEntry, context: DfaContext): DfaRunState[] {
    if (state.kind === "standard") {
        const node = context.nodes[state.index] as StandardDfaNode;
        const matches = node.transitions.filter(t => 
            t.kind === entry.kind && 
            channelsMatch(t.channel, entry.channel)
        );
        return matches.map(match => initRunState(match.targetIndex, context));
    }
    
    if (state.kind === "concurrent") {
        const node = context.nodes[state.index] as ConcurrentDfaNode;
        const results: DfaRunState[] = [];

        if (entry.channel.length > 0) {
            const key = entry.channel[0];
            const subState = state.machines[key];
            if (subState) {
                const strippedEntry: TranscriptEntry = {
                    kind: entry.kind,
                    channel: entry.channel.slice(1)
                };
                const nextSubs = transitionRunState(subState, strippedEntry, context);
                for (const ns of nextSubs) {
                    results.push({
                        kind: "concurrent",
                        index: state.index,
                        machines: {
                            ...state.machines,
                            [key]: ns
                        }
                    });
                }
            }
        }

        const allSubCompleted = Object.values(state.machines).every(s => isRunStateCompleted(s, context));
        if (allSubCompleted && node.continuationIndex !== undefined) {
            results.push(...transitionRunState(initRunState(node.continuationIndex, context), entry, context));
        }

        return results;
    }

    if (state.kind === "indexed") {
        const node = context.nodes[state.index] as IndexedDfaNode;
        const results: DfaRunState[] = [];

        if (entry.channel.length > 0) {
            const index = entry.channel[0];
            const suffix = entry.channel.slice(1);
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: suffix
            };

            if (state.active[index]) {
                const nextSubs = transitionRunState(state.active[index], strippedEntry, context);
                for (const ns of nextSubs) {
                    const active = { ...state.active };
                    if (isRunStateCompleted(ns, context)) {
                        delete active[index];
                    } else {
                        active[index] = ns;
                    }
                    results.push({
                        kind: "indexed",
                        index: state.index,
                        active,
                        activated: true
                    });
                }
            } else {
                let allowed = true;
                if (index.startsWith("*")) {
                    const starCount = Object.keys(state.active).filter(k => k.startsWith("*")).length;
                    if (starCount >= 3) {
                        allowed = false;
                    }
                }
                if (allowed) {
                    const innerStart = initRunState(node.innerStartIndex, context);
                    const nextSubs = transitionRunState(innerStart, strippedEntry, context);
                    for (const ns of nextSubs) {
                        const active = { ...state.active };
                        if (!isRunStateCompleted(ns, context)) {
                            active[index] = ns;
                        }
                        results.push({
                            kind: "indexed",
                            index: state.index,
                            active,
                            activated: true
                        });
                    }
                }
            }
        }

        const allActiveCompleted = Object.values(state.active).every(s => isRunStateCompleted(s, context));
        if (state.activated && allActiveCompleted && node.continuationIndex !== undefined) {
            results.push(...transitionRunState(initRunState(node.continuationIndex, context), entry, context));
        }

        return results;
    }

    if (state.kind === "complement") {
        const reversedEntry: TranscriptEntry = {
            kind: entry.kind === "read" ? "write" : "read",
            channel: entry.channel
        };
        const nextInners = transitionRunState(state.inner, reversedEntry, context);
        return nextInners.map(ni => ({ kind: "complement", inner: ni }));
    }

    if (state.kind === "rename") {
        const innerChannel = translateOuterToInner(entry.channel, state.mapping);
        if (innerChannel === null) return [];
        const strippedEntry: TranscriptEntry = {
            kind: entry.kind,
            channel: innerChannel
        };
        const nextInners = transitionRunState(state.inner, strippedEntry, context);
        return nextInners.map(ni => ({ kind: "rename", inner: ni, mapping: state.mapping }));
    }

    if (state.kind === "prefix") {
        const suffix = getSuffix(entry.channel, state.prefix);
        if (suffix === null) return [];
        const strippedEntry: TranscriptEntry = {
            kind: entry.kind,
            channel: suffix
        };
        const nextInners = transitionRunState(state.inner, strippedEntry, context);
        return nextInners.map(ni => ({ kind: "prefix", inner: ni, prefix: state.prefix }));
    }

    return [];
}

function getRunStateTransitions(state: DfaRunState, context: DfaContext): TranscriptEntry[] {
    if (state.kind === "standard") {
        const node = context.nodes[state.index] as StandardDfaNode;
        return node.transitions.map(t => ({ kind: t.kind, channel: t.channel }));
    }
    
    if (state.kind === "concurrent") {
        const node = context.nodes[state.index] as ConcurrentDfaNode;
        const result: TranscriptEntry[] = [];
        for (const [key, subState] of Object.entries(state.machines)) {
            for (const t of getRunStateTransitions(subState, context)) {
                result.push({ kind: t.kind, channel: [key, ...t.channel] });
            }
        }
        
        const allSubCompleted = Object.values(state.machines).every(s => isRunStateCompleted(s, context));
        if (allSubCompleted && node.continuationIndex !== undefined) {
            result.push(...getRunStateTransitions(initRunState(node.continuationIndex, context), context));
        }

        const seen = new Set<string>();
        return result.filter(ev => {
            const key = `${ev.kind}:${ev.channel.join(".")}`;
            if (seen.has(key)) return false;
            seen.add(key);
            return true;
        });
    }

    if (state.kind === "complement") {
        return getRunStateTransitions(state.inner, context).map(t => ({
            kind: t.kind === "read" ? "write" : "read",
            channel: t.channel
        }));
    }

    if (state.kind === "rename") {
        return getRunStateTransitions(state.inner, context).map(t => ({
            kind: t.kind,
            channel: translateInnerToOuter(t.channel, state.mapping)
        }));
    }

    if (state.kind === "prefix") {
        return getRunStateTransitions(state.inner, context).map(t => ({
            kind: t.kind,
            channel: [...state.prefix, ...t.channel]
        }));
    }

    if (state.kind === "indexed") {
        const node = context.nodes[state.index] as IndexedDfaNode;
        const result: TranscriptEntry[] = [];

        for (const [key, subState] of Object.entries(state.active)) {
            for (const t of getRunStateTransitions(subState, context)) {
                result.push({ kind: t.kind, channel: [key, ...t.channel] });
            }
        }

        let nextKeyIdx = 0;
        while (state.active[`*${nextKeyIdx}`]) {
            nextKeyIdx++;
        }
        if (nextKeyIdx < 3) {
            const innerStart = initRunState(node.innerStartIndex, context);
            for (const t of getRunStateTransitions(innerStart, context)) {
                result.push({ kind: t.kind, channel: [`*${nextKeyIdx}`, ...t.channel] });
            }
        }

        const allActiveCompleted = Object.values(state.active).every(s => isRunStateCompleted(s, context));
        if (allActiveCompleted && node.continuationIndex !== undefined) {
            result.push(...getRunStateTransitions(initRunState(node.continuationIndex, context), context));
        }

        const seen = new Set<string>();
        return result.filter(ev => {
            const key = `${ev.kind}:${ev.channel.join(".")}`;
            if (seen.has(key)) return false;
            seen.add(key);
            return true;
        });
    }

    return [];
}

function isSubtypeCompiled(a: CompiledSpec, b: CompiledSpec): SubtypeResult {
    const visited = new Set<string>();

    function serializeRunState(state: DfaRunState): string {
        if (state.kind === "standard") return `${state.index}`;
        if (state.kind === "concurrent") {
            const subs = Object.entries(state.machines)
                .map(([k, v]) => `${k}:${serializeRunState(v)}`)
                .sort()
                .join(",");
            return `concurrent({${subs}})`;
        }
        if (state.kind === "complement") {
            return `complement(${serializeRunState(state.inner)})`;
        }
        if (state.kind === "rename") {
            return `rename(${serializeRunState(state.inner)})`;
        }
        if (state.kind === "prefix") {
            return `prefix(${serializeRunState(state.inner)})`;
        }
        if (state.kind === "indexed") {
            const subs = Object.entries(state.active)
                .map(([k, v]) => `${k}:${serializeRunState(v)}`)
                .sort()
                .join(",");
            const activePart = subs ? `{${subs}}` : "";
            const act = state.activated ? "[activated]" : "";
            return `indexed(${state.index})${activePart}${act}`;
        }
        return "";
    }

    function serializeStateSet(states: DfaRunState[]): string {
        const strs = states.map(serializeRunState);
        strs.sort();
        return strs.join(",");
    }

    function check(statesA: DfaRunState[], statesB: DfaRunState[], path: TranscriptEntry[]): SubtypeResult {
        if (statesA.length === 1 && statesA[0].kind === "indexed" && statesB.length === 1 && statesB[0].kind === "indexed") {
            const runA = statesA[0];
            const runB = statesB[0];
            const nodeA = a.context.nodes[runA.index] as IndexedDfaNode;
            const nodeB = b.context.nodes[runB.index] as IndexedDfaNode;
            
            const resInner = isSubtypeCompiled(
                { context: a.context, startIndex: nodeA.innerStartIndex },
                { context: b.context, startIndex: nodeB.innerStartIndex }
            );
            if (resInner.isSubtype === false) {
                const mappedTranscript = resInner.transcript.map(t => ({
                    kind: t.kind,
                    channel: ["*", ...t.channel]
                }));
                return {
                    isSubtype: false,
                    reason: resInner.reason,
                    transcript: [...path, ...mappedTranscript]
                };
            }
            
            if (nodeA.continuationIndex !== undefined || nodeB.continuationIndex !== undefined) {
                const doneIndexA = compile(sequence(), a.context);
                const doneIndexB = compile(sequence(), b.context);
                const idxA = nodeA.continuationIndex !== undefined ? nodeA.continuationIndex : doneIndexA;
                const idxB = nodeB.continuationIndex !== undefined ? nodeB.continuationIndex : doneIndexB;
                const resCont = isSubtypeCompiled(
                    { context: a.context, startIndex: idxA },
                    { context: b.context, startIndex: idxB }
                );
                if (!resCont.isSubtype) return resCont;
            }
            return { isSubtype: true };
        }

        const stateKey = `${serializeStateSet(statesA)}|${serializeStateSet(statesB)}`;
        if (visited.has(stateKey)) {
            return { isSubtype: true };
        }
        visited.add(stateKey);

        const completedA = statesA.some(s => isRunStateCompleted(s, a.context));
        const completedB = statesB.some(s => isRunStateCompleted(s, b.context));

        if (completedB && !completedA) {
            return { isSubtype: false, reason: "completion", transcript: path };
        }

        const possibleB: TranscriptEntry[] = [];
        for (const sB of statesB) {
            possibleB.push(...getRunStateTransitions(sB, b.context));
        }
        const uniqueB: TranscriptEntry[] = [];
        const seenB = new Set<string>();
        for (const ev of possibleB) {
            const key = `${ev.kind}:${ev.channel.join(".")}`;
            if (!seenB.has(key)) {
                seenB.add(key);
                uniqueB.push(ev);
            }
        }

        const possibleA: TranscriptEntry[] = [];
        for (const sA of statesA) {
            possibleA.push(...getRunStateTransitions(sA, a.context));
        }
        const uniqueA: TranscriptEntry[] = [];
        const seenA = new Set<string>();
        for (const ev of possibleA) {
            const key = `${ev.kind}:${ev.channel.join(".")}`;
            if (!seenA.has(key)) {
                seenA.add(key);
                uniqueA.push(ev);
            }
        }

        for (const ev of uniqueB) {
            if (ev.kind === "read") {
                const nextAs: DfaRunState[] = [];
                for (const sA of statesA) {
                    nextAs.push(...transitionRunState(sA, ev, a.context));
                }
                if (nextAs.length === 0) {
                    return { isSubtype: false, reason: "read", transcript: [...path, ev] };
                }
                
                const nextBs: DfaRunState[] = [];
                for (const sB of statesB) {
                    nextBs.push(...transitionRunState(sB, ev, b.context));
                }
                
                const res = check(nextAs, nextBs, [...path, ev]);
                if (!res.isSubtype) return res;
            }
        }

        for (const ev of uniqueA) {
            if (ev.kind === "write") {
                const nextBs: DfaRunState[] = [];
                for (const sB of statesB) {
                    nextBs.push(...transitionRunState(sB, ev, b.context));
                }
                if (nextBs.length === 0) {
                    return { isSubtype: false, reason: "write", transcript: [...path, ev] };
                }
                
                const nextAs: DfaRunState[] = [];
                for (const sA of statesA) {
                    nextAs.push(...transitionRunState(sA, ev, a.context));
                }
                
                const res = check(nextAs, nextBs, [...path, ev]);
                if (!res.isSubtype) return res;
            }
        }

        return { isSubtype: true };
    }

    const initA = [initRunState(a.startIndex, a.context)];
    const initB = [initRunState(b.startIndex, b.context)];
    return check(initA, initB, []);
}

export function isSubtype(a: CompiledSpec, b: CompiledSpec): SubtypeResult {
    return isSubtypeCompiled(a, b);
}

export function checkTranscript(spec: CompiledSpec, transcript: TranscriptEntry[]): boolean {
    let currentGlobalStates: DfaRunState[] = [initRunState(spec.startIndex, spec.context)];

    for (const entry of transcript) {
        const nextGlobals: DfaRunState[] = [];
        for (const s of currentGlobalStates) {
            nextGlobals.push(...transitionRunState(s, entry, spec.context));
        }
        currentGlobalStates = nextGlobals;
        if (currentGlobalStates.length === 0) {
            return false;
        }
    }

    return currentGlobalStates.some(s => isRunStateCompleted(s, spec.context));
}

export function serializeCompiledSpec(compiled: CompiledSpec): string {
    return compiled.context.nodes.map(node => {
        if (node.kind === "concurrent") {
            const subs = Object.entries(node.machines)
                .map(([k, v]) => `${k}:${v}`)
                .sort()
                .join(",");
            const cont = node.continuationIndex !== undefined ? `->${node.continuationIndex}` : "";
            return `${node.index}: concurrent({${subs}})${cont}`;
        }
        if (node.kind === "indexed") {
            const cont = node.continuationIndex !== undefined ? `->${node.continuationIndex}` : "";
            return `${node.index}: indexed(${node.innerStartIndex})${cont}`;
        }
        if (node.kind === "complement") {
            return `${node.index}: complement(${node.innerStartIndex})`;
        }
        if (node.kind === "rename") {
            const mappingStr = node.mapping.map(([from, to]) => `${from.join(".")}:${to.join(".")}`).join(",");
            return `${node.index}: rename({${mappingStr}},${node.innerStartIndex})`;
        }
        if (node.kind === "prefix") {
            return `${node.index}: prefix(${node.prefix.join(".")},${node.innerStartIndex})`;
        }
        const transStr = node.transitions.map(t => `${t.kind}(${t.channel.join(".")})->${t.targetIndex}`).join(", ");
        return `${node.index}${node.isCompleted ? "*" : ""}: [${transStr}]`;
    }).join("\n");
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
