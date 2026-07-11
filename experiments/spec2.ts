export type MachineSpec2 =
    | { kind: "read"; channel: string[] }
    | { kind: "write"; channel: string[] }
    | { kind: "sequence"; specs: MachineSpec2[] }
    | { kind: "choice"; choices: MachineSpec2[] }
    | { kind: "star"; inner: MachineSpec2 }
    | { kind: "concurrent"; machines: Record<string, MachineSpec2> }
    | { kind: "complement"; inner: MachineSpec2 }
    | { kind: "rename"; mapping: Array<[string[], string[]]>; inner: MachineSpec2 }
    | { kind: "prefix"; prefix: string[]; inner: MachineSpec2 }
    | { kind: "indexed"; inner: MachineSpec2; active: MachineSpec2[] }
    | { kind: "trace"; inner: MachineSpec2; pathA: string[]; pathB: string[] };

export type TranscriptEntry =
    | { kind: "read"; channel: string[] }
    | { kind: "write"; channel: string[] };

export interface DfaTransition {
    kind: "read" | "write";
    channel: string[];
    targetIndex: number;
}

export interface DfaNode {
    index: number;
    isCompleted: boolean;
    transitions: DfaTransition[];
}

export interface CompiledSpec {
    nodes: DfaNode[];
    startIndex: number;
}

export type SubtypeResult =
    | { isSubtype: true }
    | { isSubtype: false; reason: "completion" | "read" | "write"; transcript: TranscriptEntry[] };

export function channelsEqual(a: string[], b: string[]): boolean {
    if (a.length !== b.length) return false;
    return a.every((val, index) => val === b[index]);
}

export function channelsMatch(pattern: string[], actual: string[]): boolean {
    if (pattern.length !== actual.length) return false;
    return pattern.every((val, index) => val === "*" || val === actual[index]);
}

export function getSuffix(channel: string[], prefix: string[]): string[] | null {
    if (channel.length < prefix.length) return null;
    for (let i = 0; i < prefix.length; i++) {
        if (channel[i] !== prefix[i]) return null;
    }
    return channel.slice(prefix.length);
}

export function translateOuterToInner(chan: string[], mapping: Array<[string[], string[]]>): string[] | null {
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

export function translateInnerToOuter(chan: string[], mapping: Array<[string[], string[]]>): string[] {
    for (const [from, to] of mapping) {
        const suffix = getSuffix(chan, from);
        if (suffix !== null) {
            return [...to, ...suffix];
        }
    }
    return chan;
}

export function equals(a: MachineSpec2, b: MachineSpec2): boolean {
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
            if (a.active.length !== (b as typeof a).active.length) return false;
            const checked = new Array(a.active.length).fill(false);
            for (const specA of a.active) {
                let found = false;
                for (let i = 0; i < (b as typeof a).active.length; i++) {
                    if (!checked[i] && equals(specA, (b as typeof a).active[i])) {
                        checked[i] = true;
                        found = true;
                        break;
                    }
                }
                if (!found) return false;
            }
            return true;
        }
        case "trace":
            return channelsEqual(a.pathA, (b as typeof a).pathA) &&
                   channelsEqual(a.pathB, (b as typeof a).pathB) &&
                   equals(a.inner, (b as typeof a).inner);
    }
}

export function read(channel: string[]): MachineSpec2 {
    return { kind: "read", channel };
}

export function write(channel: string[]): MachineSpec2 {
    return { kind: "write", channel };
}

export function sequence(...specs: MachineSpec2[]): MachineSpec2 {
    const flat: MachineSpec2[] = [];
    for (const spec of specs) {
        if (spec.kind === "sequence") {
            flat.push(...spec.specs);
        } else {
            flat.push(spec);
        }
    }
    if (flat.length === 1) {
        return flat[0];
    }
    return { kind: "sequence", specs: flat };
}

export function choice(...specs: MachineSpec2[]): MachineSpec2 {
    const flat: MachineSpec2[] = [];
    for (const spec of specs) {
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

export function star(inner: MachineSpec2): MachineSpec2 {
    return { kind: "star", inner };
}

export function concurrent(machines: Record<string, MachineSpec2>): MachineSpec2 {
    return { kind: "concurrent", machines };
}

export function complement(inner: MachineSpec2): MachineSpec2 {
    if (inner.kind === "complement") {
        return inner.inner;
    }
    return { kind: "complement", inner };
}

export function rename(mapping: Array<[string[], string[]]>, inner: MachineSpec2): MachineSpec2 {
    if (mapping.length === 0) {
        return inner;
    }
    return { kind: "rename", mapping, inner };
}

export function prefix(prefixPath: string[], inner: MachineSpec2): MachineSpec2 {
    if (prefixPath.length === 0) {
        return inner;
    }
    if (inner.kind === "prefix") {
        return { kind: "prefix", prefix: [...prefixPath, ...inner.prefix], inner: inner.inner };
    }
    return { kind: "prefix", prefix: prefixPath, inner };
}

export function indexed(inner: MachineSpec2): MachineSpec2 {
    return { kind: "indexed", inner, active: [] };
}

export function trace(pathA: string[], pathB: string[], inner: MachineSpec2): MachineSpec2 {
    return { kind: "trace", inner, pathA, pathB };
}

export function isCompleted(spec: MachineSpec2): boolean {
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
        case "indexed":
            return spec.active.every(isCompleted);
        case "trace": {
            const closure = resolveEpsilonTransitions([spec.inner], spec.pathA, spec.pathB);
            return closure.some(isCompleted);
        }
    }
}

export function transition(spec: MachineSpec2, entry: TranscriptEntry): MachineSpec2[] {
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
            const results: MachineSpec2[] = [];
            for (const choiceSpec of spec.choices) {
                results.push(...transition(choiceSpec, entry));
            }
            return results;
        }
        case "sequence": {
            const results: MachineSpec2[] = [];
            for (let i = 0; i < spec.specs.length; i++) {
                const head = spec.specs[i];
                const tail = spec.specs.slice(i + 1);

                const headTransitions = transition(head, entry);
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
            return transition(spec.inner, entry)
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
            return transition(sub, strippedEntry).map(nextSub => ({
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
            return transition(spec.inner, reversedEntry).map(nextInner => complement(nextInner));
        }
        case "rename": {
            const innerChannel = translateOuterToInner(entry.channel, spec.mapping);
            if (innerChannel === null) return [];
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: innerChannel
            };
            return transition(spec.inner, strippedEntry).map(nextInner => rename(spec.mapping, nextInner));
        }
        case "prefix": {
            const suffix = getSuffix(entry.channel, spec.prefix);
            if (suffix === null) return [];
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: suffix
            };
            return transition(spec.inner, strippedEntry).map(nextInner => prefix(spec.prefix, nextInner));
        }
        case "indexed": {
            if (entry.channel.length === 0) return [];
            const index = entry.channel[0];
            const suffix = entry.channel.slice(1);
            const strippedEntry: TranscriptEntry = {
                kind: entry.kind,
                channel: suffix
            };

            const results: MachineSpec2[] = [];

            // 1. Transition one of the active instances
            for (let i = 0; i < spec.active.length; i++) {
                const subSpec = spec.active[i];
                const nextSubs = transition(subSpec, strippedEntry);
                for (const nextSub of nextSubs) {
                    const active = [...spec.active];
                    if (isCompleted(nextSub)) {
                        active.splice(i, 1);
                    } else {
                        active[i] = nextSub;
                    }
                    results.push({
                        kind: "indexed",
                        inner: spec.inner,
                        active
                    });
                }
            }

            // 2. Spawn a new instance of inner (limit to at most 3 concurrent active instances to keep state space finite)
            if (spec.active.length < 3) {
                const nextInnerSubs = transition(spec.inner, strippedEntry);
                for (const nextSub of nextInnerSubs) {
                    const active = [...spec.active];
                    if (!isCompleted(nextSub)) {
                        active.push(nextSub);
                    }
                    results.push({
                        kind: "indexed",
                        inner: spec.inner,
                        active
                    });
                }
            }

            return results;
        }
        case "trace": {
            if (getSuffix(entry.channel, spec.pathA) !== null || getSuffix(entry.channel, spec.pathB) !== null) {
                return [];
            }
            const closure = resolveEpsilonTransitions([spec.inner], spec.pathA, spec.pathB);
            const results: MachineSpec2[] = [];
            for (const s of closure) {
                const nextStates = transition(s, entry);
                for (const nextState of nextStates) {
                    results.push(trace(spec.pathA, spec.pathB, nextState));
                }
            }
            return results;
        }
    }
}

export function getPossibleTransitions(spec: MachineSpec2): TranscriptEntry[] {
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
            for (const sub of spec.active) {
                for (const t of getPossibleTransitions(sub)) {
                    result.push({ kind: t.kind, channel: ["*", ...t.channel] });
                }
            }
            for (const t of getPossibleTransitions(spec.inner)) {
                result.push({ kind: t.kind, channel: ["*", ...t.channel] });
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

export function serializeSpec(spec: MachineSpec2): string {
    switch (spec.kind) {
        case "read":
            return `read(${spec.channel.join(".")})`;
        case "write":
            return `write(${spec.channel.join(".")})`;
        case "sequence":
            return `seq(${spec.specs.map(serializeSpec).join(",")})`;
        case "choice":
            return `choice(${spec.choices.map(serializeSpec).join(",")})`;
        case "star":
            return `star(${serializeSpec(spec.inner)})`;
        case "concurrent": {
            const subs = Object.entries(spec.machines)
                .map(([k, v]) => `${k}:${serializeSpec(v)}`)
                .sort()
                .join(",");
            return `concurrent({${subs}})`;
        }
        case "complement":
            return `complement(${serializeSpec(spec.inner)})`;
        case "rename": {
            const mappingsStr = spec.mapping.map(([from, to]) => `${from.join(".")}:${to.join(".")}`).join(",");
            return `rename({${mappingsStr}},${serializeSpec(spec.inner)})`;
        }
        case "prefix":
            return `prefix(${spec.prefix.join(".")},${serializeSpec(spec.inner)})`;
        case "indexed": {
            const activeStr = spec.active.map(serializeSpec).sort().join(",");
            const activePart = activeStr ? `{${activeStr}}` : "";
            return `indexed(${serializeSpec(spec.inner)})${activePart}`;
        }
        case "trace":
            return `trace(${serializeSpec(spec.inner)},${spec.pathA.join(".")},${spec.pathB.join(".")})`;
    }
}

function deduplicateStates(states: MachineSpec2[]): MachineSpec2[] {
    const result: MachineSpec2[] = [];
    for (const state of states) {
        if (!result.some(r => equals(r, state))) {
            result.push(state);
        }
    }
    return result;
}

export function stateSetsEqual(a: MachineSpec2[], b: MachineSpec2[]): boolean {
    if (a.length !== b.length) return false;
    return a.every(x => b.some(y => equals(x, y)));
}

export function resolveEpsilonTransitions(states: MachineSpec2[], pathA: string[], pathB: string[]): MachineSpec2[] {
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

                    const intermediateStates = transition(current, ev);
                    for (const s1 of intermediateStates) {
                        const nextStates = transition(s1, readEvent);
                        for (const s2 of nextStates) {
                            if (!closure.some(c => equals(c, s2))) {
                                closure.push(s2);
                                queue.push(s2);
                            }
                        }
                    }
                }

                const suffixB = getSuffix(ev.channel, pathB);
                if (suffixB !== null) {
                    const readChannel = [...pathA, ...suffixB];
                    const readEvent: TranscriptEntry = { kind: "read", channel: readChannel };

                    const intermediateStates = transition(current, ev);
                    for (const s1 of intermediateStates) {
                        const nextStates = transition(s1, readEvent);
                        for (const s2 of nextStates) {
                            if (!closure.some(c => equals(c, s2))) {
                                closure.push(s2);
                                queue.push(s2);
                            }
                        }
                    }
                }
            }
        }
    }
    return closure;
}

export function compile(spec: MachineSpec2): CompiledSpec {
    const nodes: DfaNode[] = [];
    const nodeStates: MachineSpec2[][] = [];

    function getOrCreateNodeIndex(states: MachineSpec2[]): number {
        for (let i = 0; i < nodeStates.length; i++) {
            if (stateSetsEqual(nodeStates[i], states)) {
                return i;
            }
        }
        const index = nodes.length;
        nodeStates.push(states);
        nodes.push({
            index,
            isCompleted: states.some(isCompleted),
            transitions: []
        });
        return index;
    }

    const initialStates = deduplicateStates([spec]);
    const startIndex = getOrCreateNodeIndex(initialStates);

    let processedCount = 0;
    while (processedCount < nodes.length) {
        const currentIndex = processedCount;
        processedCount++;

        const currentNfaStates = nodeStates[currentIndex];
        const node = nodes[currentIndex];

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
            const nextStatesRaw: MachineSpec2[] = [];
            for (const s of currentNfaStates) {
                nextStatesRaw.push(...transition(s, entry));
            }
            const nextStates = deduplicateStates(nextStatesRaw);
            if (nextStates.length > 0) {
                const targetIndex = getOrCreateNodeIndex(nextStates);
                node.transitions.push({
                    kind: entry.kind,
                    channel: entry.channel,
                    targetIndex
                });
            }
        }
    }

    return {
        nodes,
        startIndex
    };
}

export function isSubtype(a: CompiledSpec, b: CompiledSpec): SubtypeResult {
    const visited = new Set<string>();

    function check(indexA: number, indexB: number, path: TranscriptEntry[]): SubtypeResult {
        const stateKey = `${indexA}|${indexB}`;
        if (visited.has(stateKey)) {
            return { isSubtype: true };
        }
        visited.add(stateKey);

        const nodeA = a.nodes[indexA];
        const nodeB = b.nodes[indexB];

        if (nodeB.isCompleted && !nodeA.isCompleted) {
            return { isSubtype: false, reason: "completion", transcript: path };
        }

        // 1. Contravariant Inputs (Reads): every input that B accepts, A must also accept
        for (const tb of nodeB.transitions) {
            if (tb.kind === "read") {
                const ta = nodeA.transitions.find(t => t.kind === "read" && channelsEqual(t.channel, tb.channel));
                if (!ta) {
                    return { isSubtype: false, reason: "read", transcript: [...path, { kind: "read", channel: tb.channel }] };
                }
                const result = check(ta.targetIndex, tb.targetIndex, [...path, { kind: "read", channel: tb.channel }]);
                if (!result.isSubtype) {
                    return result;
                }
            }
        }

        // 2. Covariant Outputs (Writes): every output that A produces, B must also allow/expect
        for (const ta of nodeA.transitions) {
            if (ta.kind === "write") {
                const tb = nodeB.transitions.find(t => t.kind === "write" && channelsEqual(t.channel, ta.channel));
                if (!tb) {
                    return { isSubtype: false, reason: "write", transcript: [...path, { kind: "write", channel: ta.channel }] };
                }
                const result = check(ta.targetIndex, tb.targetIndex, [...path, { kind: "write", channel: ta.channel }]);
                if (!result.isSubtype) {
                    return result;
                }
            }
        }

        return { isSubtype: true };
    }

    return check(a.startIndex, b.startIndex, []);
}

export function checkTranscript(compiled: CompiledSpec, transcript: TranscriptEntry[]): boolean {
    let currentIndex = compiled.startIndex;
    for (const entry of transcript) {
        const currentNode = compiled.nodes[currentIndex];
        let transitionFound = false;
        for (const t of currentNode.transitions) {
            if (t.kind === entry.kind && channelsMatch(t.channel, entry.channel)) {
                currentIndex = t.targetIndex;
                transitionFound = true;
                break;
            }
        }
        if (!transitionFound) {
            return false;
        }
    }
    return compiled.nodes[currentIndex].isCompleted;
}

export function serializeCompiledSpec(compiled: CompiledSpec): string {
    return compiled.nodes.map(node => {
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
