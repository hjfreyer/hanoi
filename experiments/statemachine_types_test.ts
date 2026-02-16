
declare global {
    namespace jest {
        interface Matchers<R> {
            toMatchTranscript(transcript: string[]): R;
        }
    }
}

type MachineType = {
    kind: 'sequence',
    inner: MachineType[]
} | {
    kind: 'choice',
    choices: MachineChoice[],
} | {
    kind: 'loop',
    inner: (m : MachineType) => MachineType
} | {
    kind: 'product',
    inner: Record<string, MachineType>,
} | {
    kind: 'reverse',
    inner: MachineType,
};

type MachineChoice = {
    direction: Direction;
    channel: string;
    inner: MachineType;
};

type Direction = 'in' | 'out';

type TranscriptEntry = {
    direction: Direction;
    channel: string;
};

/// Parses matcher strings ">foo" (in) or "<foo" (out). The whole string after the prefix is the channel.
function parseMatcherStrings(strings: string[]): TranscriptEntry[] {
    return strings.map((s) => {
        if (s.length < 2 || (s[0] !== '>' && s[0] !== '<')) {
            throw new Error(`Matcher entry must be ">foo" (in) or "<foo" (out), got: ${JSON.stringify(s)}`);
        }
        const direction: Direction = s[0] === '>' ? 'in' : 'out';
        const channel = s.slice(1);
        return { direction, channel };
    });
}

type PrefixResult = { kind: 'ok'; remainder: TranscriptEntry[] } | { kind: 'error'; reason: string };

function formatEntry(e: TranscriptEntry): string {
    return (e.direction === 'in' ? '>' : '<') + e.channel;
}

/// Returns the remainder of transcript after m consumes a prefix, or an error reason if no valid prefix.
function validatePrefix(m: MachineType, transcript: TranscriptEntry[]): PrefixResult {
    if (m.kind === 'sequence') {
        let rest: TranscriptEntry[] = transcript;
        for (let i = 0; i < m.inner.length; i++) {
            const next = validatePrefix(m.inner[i], rest);
            if (next.kind === 'error') {
                return { kind: 'error', reason: `at sequence step ${i + 1}: ${next.reason}` };
            }
            rest = next.remainder;
        }
        return { kind: 'ok', remainder: rest };
    }
    if (m.kind === 'choice') {
        if (transcript.length === 0) {
            const expected = m.choices.map((c) => (c.direction === 'in' ? '>' : '<') + c.channel).join(', ');
            return { kind: 'error', reason: `expected one of [${expected}], got end of transcript` };
        }
        const entry = transcript[0];
        const match = m.choices.find((c) => c.direction === entry.direction && c.channel === entry.channel);
        if (match === undefined) {
            const expected = m.choices.map((c) => (c.direction === 'in' ? '>' : '<') + c.channel).join(', ');
            return { kind: 'error', reason: `expected one of [${expected}], got '${formatEntry(entry)}'` };
        }
        const rest = transcript.slice(1);
        const out = validatePrefix(match.inner, rest);
        if (out.kind === 'error') {
            return { kind: 'error', reason: `in choice branch '${formatEntry(entry)}': ${out.reason}` };
        }
        return out;
    }
    if (m.kind === 'loop') {
        const loopBody = m.inner(m);
        const out = validatePrefix(loopBody, transcript);
        if (out.kind === 'error') {
            return { kind: 'error', reason: `in loop: ${out.reason}` };
        }
        return out;
    }
    if (m.kind === 'product') {
        const channelNames = Object.keys(m.inner);
        let lastError: string | null = null;
        for (let k = 0; k <= transcript.length; k++) {
            const prefix = transcript.slice(0, k);
            const tokensByChannel: Record<string, TranscriptEntry[]> = {};
            for (const ch of channelNames) tokensByChannel[ch] = [];
            let invalid = false;
            let invalidEntry: TranscriptEntry | null = null;
            for (const entry of prefix) {
                // Product entries have channel "name/rest" (e.g. "left/a" or "cmp/left/t0/get"); split to route to inner channel.
                const slash = entry.channel.indexOf('/');
                if (slash < 0) {
                    invalid = true;
                    invalidEntry = entry;
                    break;
                }
                const ch = entry.channel.slice(0, slash);
                const token = entry.channel.slice(slash + 1);
                if (m.inner[ch] === undefined) {
                    invalid = true;
                    invalidEntry = entry;
                    break;
                }
                tokensByChannel[ch].push({ direction: entry.direction, channel: token });
            }
            if (invalid && invalidEntry) {
                lastError = `invalid entry '${formatEntry(invalidEntry)}' (expected channel in [${channelNames.join(', ')}])`;
                continue;
            }
            let channelFailed = false;
            for (const ch of channelNames) {
                const res = validateTranscript(m.inner[ch], tokensByChannel[ch] ?? []);
                if (res.matched === false) {
                    lastError = `channel '${ch}': ${res.reason}`;
                    channelFailed = true;
                    break;
                }
            }
            if (!channelFailed) return { kind: 'ok', remainder: transcript.slice(k) };
        }
        return { kind: 'error', reason: lastError ?? `product: no valid split (channels: [${channelNames.join(', ')}])` };
    }
    if (m.kind === 'reverse') {
        const flipped = transcript.map((e) => ({ ...e, direction: (e.direction === 'in' ? 'out' : 'in') as Direction }));
        const out = validatePrefix(m.inner, flipped);
        if (out.kind === 'error') {
            return { kind: 'error', reason: `in reverse: ${out.reason}` };
        }
        const remainder = out.remainder.map((e) => ({ ...e, direction: (e.direction === 'in' ? 'out' : 'in') as Direction }));
        return { kind: 'ok', remainder };
    }
    throw new Error(`Unknown machine kind`);
}

export type ValidateResult = { matched: true } | { matched: false; reason: string };

/// Returns whether the transcript matches the machine, and if not, an explanation.
/// Every transcript must start with ">START" and end with "<END".
function validateTranscript(m: MachineType, transcript: TranscriptEntry[]): ValidateResult {
    if (transcript.length < 2) {
        return { matched: false, reason: 'transcript must start with >START and end with <END' };
    }
    if (transcript[0].direction !== 'in' || transcript[0].channel !== 'START') {
        return { matched: false, reason: `transcript must start with >START, got '${formatEntry(transcript[0])}'` };
    }
    const last = transcript[transcript.length - 1];
    if (last.direction !== 'out' || last.channel !== 'END') {
        return { matched: false, reason: `transcript must end with <END, got '${formatEntry(last)}'` };
    }
    const middle = transcript.slice(1, -1);
    const prefixResult = validatePrefix(m, middle);
    if (prefixResult.kind === 'error') {
        return { matched: false, reason: prefixResult.reason };
    }
    if (prefixResult.remainder.length > 0) {
        const extra = prefixResult.remainder.length > 5
            ? prefixResult.remainder.slice(0, 5).map(formatEntry).join(', ') + ', ...'
            : prefixResult.remainder.map(formatEntry).join(', ');
        return { matched: false, reason: `expected end of transcript, got ${prefixResult.remainder.length} extra token(s): ${extra}` };
    }
    return { matched: true };
}

/// Jest matcher: expect(machine).toMatchTranscript(transcript). transcript is string[] of form ">foo" (in) or "<foo" (out). Asserts match and prints validation reason on failure.
expect.extend({
    toMatchTranscript(
        this: { isNot?: boolean },
        received: MachineType,
        transcript: string[],
    ): jest.CustomMatcherResult {
        const entries = parseMatcherStrings(transcript);
        const result = validateTranscript(received, entries);
        if (result.matched) {
            return { pass: true, message: () => '' };
        }
        const reason = (result as { matched: false; reason: string }).reason;
        return {
            pass: false,
            message: () =>
                this.isNot
                    ? `Expected transcript not to match, but it did.`
                    : `Expected transcript to match, but:\n${reason}`,
        };
    },
});

describe('validateTranscript', () => {
    it('validates single token', () => {
        expect(receive('x')).toMatchTranscript(['>START', '>x', '<END']);
        expect(receive('x')).not.toMatchTranscript([]);
        expect(receive('x')).not.toMatchTranscript(['>START', '>y', '<END']);
        expect(receive('x')).not.toMatchTranscript(['>START', '>x', '>x', '<END']);
    });

    it('validates sequence', () => {
        const m = sequence(receive('a'), receive('b'), receive('c'));
        expect(m).toMatchTranscript(['>START', '>a', '>b', '>c', '<END']);
        expect(m).not.toMatchTranscript(['>START', '>a', '>b', '<END']);
        expect(m).not.toMatchTranscript(['>START', '>b', '>a', '>c', '<END']);
        expect(m).not.toMatchTranscript([]);
    });

    it('validates empty sequence (accepts only empty transcript)', () => {
        const m = { kind: 'sequence' as const, inner: [] };
        expect(m).toMatchTranscript(['>START', '<END']);
        expect(m).not.toMatchTranscript(['>START', '>x', '<END']);
    });

    it('validates choice', () => {
        const m = choice({ '>a': sequence(), '>b': sequence(), '>c': sequence() });
        expect(m).toMatchTranscript(['>START', '>a', '<END']);
        expect(m).toMatchTranscript(['>START', '>b', '<END']);
        expect(m).toMatchTranscript(['>START', '>c', '<END']);
        expect(m).not.toMatchTranscript(['>START', '>d', '<END']);
        expect(m).not.toMatchTranscript([]);
    });

    it('validates choice direction (rejects wrong direction)', () => {
        const m = choice({ '>a': sequence(), '<b': sequence() });
        expect(m).toMatchTranscript(['>START', '>a', '<END']);
        expect(m).toMatchTranscript(['>START', '<b', '<END']);
        expect(m).not.toMatchTranscript(['>START', '<a', '<END']);
        expect(m).not.toMatchTranscript(['>START', '>b', '<END']);
    });

    it('reverse flips direction of all messages', () => {
        const m = reverse(receive('x'));
        expect(m).toMatchTranscript(['>START', '<x', '<END']);
        expect(m).not.toMatchTranscript(['>START', '>x', '<END']);
        expect(m).not.toMatchTranscript(['>START', '<y', '<END']);
        const m2 = reverse(sequence(receive('a'), receive('b')));
        expect(m2).toMatchTranscript(['>START', '<a', '<b', '<END']);
        expect(m2).not.toMatchTranscript(['>START', '>a', '>b', '<END']);
    });

    it('validates loop with multiple tokens', () => {
        const m: MachineType = {
            kind: 'loop',
            inner: (self) => choice({
                '>ping': sequence(receive('pong'), self),
                '>end': sequence(),
            }),
        };
        expect(m).toMatchTranscript(['>START', '>end', '<END']);
        expect(m).toMatchTranscript(['>START', '>ping', '>pong', '>end', '<END']);
        expect(m).toMatchTranscript(['>START', '>ping', '>pong', '>ping', '>pong', '>end', '<END']);
    });

    it('loop with no way to terminate does not match finite transcript', () => {
        const m: MachineType = {
            kind: 'loop',
            inner: (self) => sequence(receive('ping'), receive('pong'), self),
        };
        expect(m).not.toMatchTranscript(['>START', '>ping', '>pong', '<END']);
    });
});

describe('product (MachineType)', () => {
    it('validates product with left/ and right/ prefixed tokens', () => {
        const m = product({ left: receive('a'), right: receive('b') });
        expect(m).toMatchTranscript(['>START', '>left/START', '>left/a', '<left/END', '>right/START', '>right/b', '<right/END', '<END']);
        expect(m).toMatchTranscript(['>START', '>right/START', '>right/b', '<right/END', '>left/START', '>left/a', '<left/END', '<END']);
    });

    it('rejects tokens without left/ or right/ prefix', () => {
        const m = product({ left: receive('a'), right: receive('b') });
        expect(m).not.toMatchTranscript(['>START', '>a', '>right/START', '>right/b', '<right/END', '<END']);
        expect(m).not.toMatchTranscript(['>START', '>left/START', '>left/a', '<left/END', '>b', '<END']);
    });

    it('validates product of sequence machines', () => {
        const left = sequence(receive('x'), receive('y'));
        const right = sequence(receive('a'), receive('b'));
        const m = product({ left, right });
        expect(m).toMatchTranscript(['>START', '>left/START', '>left/x', '>left/y', '<left/END', '>right/START', '>right/a', '>right/b', '<right/END', '<END']);
    });

    it('rejects when left or right stream is invalid', () => {
        const m = product({ left: receive('a'), right: receive('b') });
        expect(m).not.toMatchTranscript(['>START', '>left/START', '>left/wrong', '<left/END', '>right/START', '>right/b', '<right/END', '<END']);
        expect(m).not.toMatchTranscript(['>START', '>left/START', '>left/a', '<left/END', '>right/START', '>right/wrong', '<right/END', '<END']);
    });

    it('accepts empty transcript when both sides accept empty', () => {
        const m = product({
            left: { kind: 'sequence', inner: [] },
            right: { kind: 'sequence', inner: [] },
        });
        expect(m).toMatchTranscript(['>START', '>left/START', '<left/END', '>right/START', '<right/END', '<END']);
    });

    it('sequence(A, product(B, C), D) leaves remainder for D', () => {
        const m = sequence(
            receive('a'),
            product({ left: receive('b'), right: receive('c') }),
            receive('d'),
        );
        expect(m).toMatchTranscript(['>START', '>a', '>left/START', '>left/b', '<left/END', '>right/START', '>right/c', '<right/END', '>d', '<END']);
        expect(m).not.toMatchTranscript(['>START', '>a', '>left/START', '>left/b', '<left/END', '>right/START', '>right/c', '<right/END', '<END']);
    });

    it('sequence(product(A, B), product(C, D), E) two products in a row', () => {
        const m = sequence(
            product({ left: receive('a'), right: receive('b') }),
            product({ left: receive('c'), right: receive('d') }),
            receive('e'),
        );
        expect(m).toMatchTranscript(['>START', '>left/START', '>left/a', '<left/END', '>right/START', '>right/b', '<right/END', '>left/START', '>left/c', '<left/END', '>right/START', '>right/d', '<right/END', '>e', '<END']);
        expect(m).not.toMatchTranscript(['>START', '>left/START', '>left/a', '<left/END', '>right/START', '>right/b', '<right/END', '>left/START', '>left/c', '<left/END', '>right/START', '>right/d', '<right/END', '<END']);
    });
});

function sequence(...machines: MachineType[]): MachineType {    
    return {
        kind: 'sequence',
        inner: machines,
    };
}

/// Dict key is ">channel" (in) or "<channel" (out); value is the machine for that choice.
function choice(choices: Record<string, MachineType>): MachineType {
    return {
        kind: 'choice',
        choices: Object.entries(choices).map(([prefix, inner]) => {
            if (prefix.length < 2 || (prefix[0] !== '>' && prefix[0] !== '<')) {
                throw new Error(`Choice key must be ">channel" or "<channel", got: ${JSON.stringify(prefix)}`);
            }
            const direction: Direction = prefix[0] === '>' ? 'in' : 'out';
            const channel = prefix.slice(1);
            return { direction, channel, inner };
        }),
    };
}

function receive(t: string): MachineType {
    return choice({ ['>' + t]: sequence() });
}

function emit(t: string): MachineType {
    return choice({ ['<' + t]: sequence() });
}

function loop(f: (self: MachineType) => MachineType): MachineType {
    return {
        kind: 'loop',
        inner: f,
    };
}

function reverse(inner: MachineType): MachineType {
    return { kind: 'reverse', inner };
}

function product(inner: Record<string, MachineType>): MachineType {
    return {
        kind: 'product',
        inner,
    };
}

function pinPad(onCorrect:MachineType): MachineType {
    return loop((self) => sequence(
        receive('enterDigit'),
        receive('enterDigit'),
        receive('enterDigit'),
        receive('enterDigit'),
        choice({
            '<correct': sequence(onCorrect),
            '<incorrect': sequence(self),
        }),
    ));
}

const secureDoor = pinPad(
    sequence(
        receive('pull'),
        emit('doorOpen'),
    ),
);

describe('secureDoor', () => {
    it('accepts four digits then correct, pull, doorOpen', () => {
        expect(secureDoor).toMatchTranscript([
            '>START', '>enterDigit', '>enterDigit', '>enterDigit', '>enterDigit',
            '<correct', '>pull', '<doorOpen', '<END',
        ]);
    });

    it('accepts four digits then incorrect then retry and succeed', () => {
        expect(secureDoor).toMatchTranscript([
            '>START', '>enterDigit', '>enterDigit', '>enterDigit', '>enterDigit',
            '<incorrect',
            '>enterDigit', '>enterDigit', '>enterDigit', '>enterDigit',
            '<correct', '>pull', '<doorOpen', '<END',
        ]);
    });

    it('accepts multiple wrong attempts then succeed', () => {
        expect(secureDoor).toMatchTranscript([
            '>START', '>enterDigit', '>enterDigit', '>enterDigit', '>enterDigit', '<incorrect',
            '>enterDigit', '>enterDigit', '>enterDigit', '>enterDigit', '<incorrect',
            '>enterDigit', '>enterDigit', '>enterDigit', '>enterDigit',
            '<correct', '>pull', '<doorOpen', '<END',
        ]);
    });

    it('rejects fewer than four digits before correct path', () => {
        expect(secureDoor).not.toMatchTranscript([
            '>START', '>enterDigit', '>enterDigit', '>enterDigit',
            '<correct', '>pull', '<doorOpen', '<END',
        ]);
    });

    it('rejects wrong order (e.g. doorOpen before pull)', () => {
        expect(secureDoor).not.toMatchTranscript([
            '>START', '>enterDigit', '>enterDigit', '>enterDigit', '>enterDigit',
            '<correct', '<doorOpen', '>pull', '<END',
        ]);
    });

    it('rejects correct without pull and doorOpen', () => {
        expect(secureDoor).not.toMatchTranscript([
            '>START', '>enterDigit', '>enterDigit', '>enterDigit', '>enterDigit',
            '<correct', '<END',
        ]);
    });

    it('rejects four digits only (no correct/incorrect outcome)', () => {
        expect(secureDoor).not.toMatchTranscript(['>START', '>enterDigit', '>enterDigit', '>enterDigit', '>enterDigit', '<END']);
    });
});

const ref = loop((self) => choice({ '>close': sequence(), '>get': sequence(receive('result'), self) }));

function comparator(t: MachineType) : MachineType {
    return loop((self) =>
        choice({
            '>cmp': sequence(
                product({
                    'left': t,
                    'right': t,
                }),
                emit('result'),
                self
            ),
            '>close': sequence(),
        })
    );
}

function pair(t0 : MachineType, t1 : MachineType) : MachineType {
    return product({
        't0': t0,
        't1': t1,
    });
}

describe('comparator', () => {
    it('accepts cmp then end on both refs then result', () => {
        expect(comparator(ref)).toMatchTranscript([
            '>START', '>cmp',
            '>left/START', '>left/close', '<left/END',
            '>right/START', '>right/close', '<right/END',
            '<result', '>close', '<END',
        ]);
    });

    it('accepts cmp then one get/result on left, end on right, then result', () => {
        expect(comparator(ref)).toMatchTranscript([
            '>START', '>cmp',
            '>left/START', '>left/get', '>left/result', '>left/close', '<left/END',
            '>right/START', '>right/close', '<right/END',
            '<result', '>close', '<END',
        ]);
    });

    it('accepts cmp then one get/result on right, end on left, then result', () => {
        expect(comparator(ref)).toMatchTranscript([
            '>START', '>cmp',
            '>right/START', '>right/get', '>right/result', '>right/close', '<right/END',
            '>left/START', '>left/close', '<left/END',
            '<result', '>close', '<END',
        ]);
    });

    it('accepts cmp then interleaved get/result on both sides then end then result', () => {
        expect(comparator(ref)).toMatchTranscript([
            '>START', '>cmp',
            '>left/START', '>left/get', '>left/result', '>left/close', '<left/END',
            '>right/START', '>right/get', '>right/result', '>right/close', '<right/END',
            '<result', '>close', '<END',
        ]);
    });

    it('accepts cmp then multiple get/result on both sides then end then result', () => {
        expect(comparator(ref)).toMatchTranscript([
            '>START', '>cmp',
            '>left/START', '>left/get', '>left/result', '>left/get', '>left/result', '>left/close', '<left/END',
            '>right/START', '>right/get', '>right/result', '>right/get', '>right/result', '>right/close', '<right/END',
            '<result', '>close', '<END',
        ]);
    });

    it('rejects missing cmp', () => {
        expect(comparator(ref)).not.toMatchTranscript(['>START', '<result', '<END']);
    });

    it('rejects missing final result', () => {
        expect(comparator(ref)).not.toMatchTranscript(['>START', '>cmp', '<END']);
    });

    it('rejects incomplete ref stream (get without result)', () => {
        expect(comparator(ref)).not.toMatchTranscript([
            '>START', '>cmp',
            '>left/START', '>left/get', '<left/END',
            '>right/START', '<right/END',
            '<result', '<END',
        ]);
    });

    it('rejects wrong channel prefix', () => {
        expect(comparator(ref)).not.toMatchTranscript([
            '>START', '>cmp',
            '>left/START', '>left/end', '<left/END',
            '>other/get',
            '>right/START', '>right/end', '<right/END',
            '<result', '>end', '<END',
        ]);
    });
});

function lexCompare(t0: MachineType, t1: MachineType) : MachineType {
    return product({
        cmp: comparator(pair(t0, t1)),
        t0_cmp: reverse(comparator(t0)),
        t1_cmp: reverse(comparator(t1)),
    });
}

describe('lexCompare', () => {
    it('accepts cmp then end on both refs then result', () => {
        // Sub-transcripts must explicitly START and END at every level. Top-level product: cmp, t0_cmp, t1_cmp.
        // The cmp channel runs comparator(pair(t0,t1)), which has an inner product(left, right); those need START/END too.
        expect(lexCompare(ref, ref)).toMatchTranscript([
            '>START',
            '>cmp/START', '>cmp/cmp',
            '>cmp/left/START', '<cmp/left/END',
            '>cmp/right/START', '<cmp/right/END',
            '<cmp/result', '>cmp/end',
            '<cmp/END',
            '>t0_cmp/START', '<t0_cmp/END',
            '>t1_cmp/START', '<t1_cmp/END',
            '<END',
        ]);
    });
});
