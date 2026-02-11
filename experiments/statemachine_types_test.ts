
type MachineType = {
    kind: 'sequence',
    inner: MachineType[]
} | {
    kind: 'choice',
    inner: Record<string, MachineType>
} | {
    kind: 'loop',
    inner: (m : MachineType) => MachineType
} | {
    kind: 'product',
    inner: Record<string, MachineType>,
} | {
    kind: 'emit',
    token: string,
};

type PrefixResult = { kind: 'ok'; remainder: string[] } | { kind: 'error'; reason: string };

/// Returns the remainder of transcript after m consumes a prefix, or an error reason if no valid prefix.
function validatePrefix(m: MachineType, transcript: string[]): PrefixResult {
    if (m.kind === 'emit') {
        if (transcript.length > 0 && transcript[0] === m.token) {
            return { kind: 'ok', remainder: transcript.slice(1) };
        }
        const got = transcript.length === 0 ? 'end of transcript' : `'${transcript[0]}'`;
        return { kind: 'error', reason: `expected token '${m.token}', got ${got}` };
    }
    if (m.kind === 'sequence') {
        let rest: string[] = transcript;
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
        const keys = Object.keys(m.inner);
        if (transcript.length === 0) {
            return { kind: 'error', reason: `expected one of [${keys.join(', ')}], got end of transcript` };
        }
        const machine = m.inner[transcript[0]];
        if (machine === undefined) {
            return { kind: 'error', reason: `expected one of [${keys.join(', ')}], got '${transcript[0]}'` };
        }
        const rest = transcript.slice(1);
        const out = validatePrefix(machine, rest);
        if (out.kind === 'error') {
            return { kind: 'error', reason: `in choice branch '${transcript[0]}': ${out.reason}` };
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
            const tokensByChannel: Record<string, string[]> = {};
            for (const ch of channelNames) tokensByChannel[ch] = [];
            let invalid = false;
            let invalidTag = '';
            for (const tag of prefix) {
                const slash = tag.indexOf('/');
                if (slash < 0) {
                    invalid = true;
                    invalidTag = tag;
                    break;
                }
                const channel = tag.slice(0, slash);
                const value = tag.slice(slash + 1);
                if (m.inner[channel] === undefined) {
                    invalid = true;
                    invalidTag = tag;
                    break;
                }
                tokensByChannel[channel].push(value);
            }
            if (invalid) {
                lastError = `invalid tag '${invalidTag}' (expected channel/value, channels: [${channelNames.join(', ')}])`;
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
    throw new Error(`Unknown machine kind`);
}

export type ValidateResult = { matched: true } | { matched: false; reason: string };

/// Returns whether the transcript matches the machine, and if not, an explanation.
function validateTranscript(m: MachineType, transcript: string[]): ValidateResult {
    const prefixResult = validatePrefix(m, transcript);
    if (prefixResult.kind === 'error') {
        return { matched: false, reason: prefixResult.reason };
    }
    if (prefixResult.remainder.length > 0) {
        const extra = prefixResult.remainder.length > 5
            ? prefixResult.remainder.slice(0, 5).join(', ') + ', ...'
            : prefixResult.remainder.join(', ');
        return { matched: false, reason: `expected end of transcript, got ${prefixResult.remainder.length} extra token(s): ${extra}` };
    }
    return { matched: true };
}

/// Jest matcher: expect(machine).toMatchTranscript(transcript). Asserts match and prints validation reason on failure.
expect.extend({
    toMatchTranscript(
        this: { isNot?: boolean },
        received: MachineType,
        transcript: string[],
    ): jest.CustomMatcherResult {
        const result = validateTranscript(received, transcript);
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
    const tok = (token: string): MachineType => ({ kind: 'emit', token });

    it('validates single token', () => {
        expect(tok('x')).toMatchTranscript(['x']);
        expect(tok('x')).not.toMatchTranscript([]);
        expect(tok('x')).not.toMatchTranscript(['y']);
        expect(tok('x')).not.toMatchTranscript(['x', 'x']);
    });

    it('validates sequence', () => {
        const m = sequence(tok('a'), tok('b'), tok('c'));
        expect(m).toMatchTranscript(['a', 'b', 'c']);
        expect(m).not.toMatchTranscript(['a', 'b']);
        expect(m).not.toMatchTranscript(['b', 'a', 'c']);
        expect(m).not.toMatchTranscript([]);
    });

    it('validates empty sequence (accepts only empty transcript)', () => {
        const m = { kind: 'sequence' as const, inner: [] };
        expect(m).toMatchTranscript([]);
        expect(m).not.toMatchTranscript(['x']);
    });

    it('validates choice', () => {
        const m = { kind: 'choice' as const, inner: { a: sequence(), b: sequence(), c: sequence() } };
        expect(m).toMatchTranscript(['a']);
        expect(m).toMatchTranscript(['b']);
        expect(m).toMatchTranscript(['c']);
        expect(m).not.toMatchTranscript(['d']);
        expect(m).not.toMatchTranscript([]);
    });

    it('validates loop with multiple tokens', () => {
        const m: MachineType = {
            kind: 'loop',
            inner: (self) => choice({
                'ping': sequence(tok('pong'), self),
                'end': sequence(),
            }),
        };
        expect(m).toMatchTranscript(['end']);
        expect(m).toMatchTranscript(['ping', 'pong', 'end']);
        expect(m).toMatchTranscript(['ping', 'pong', 'ping', 'pong', 'end']);
    });

    it('loop with no way to terminate does not match finite transcript', () => {
        const m: MachineType = {
            kind: 'loop',
            inner: (self) => sequence(tok('ping'), tok('pong'), self),
        };
        expect(m).not.toMatchTranscript(['ping', 'pong']);
    });
});

describe('product (MachineType)', () => {
    const tok = (token: string): MachineType => ({ kind: 'emit', token });

    it('validates product with left/ and right/ prefixed tokens', () => {
        const m = product({ left: tok('a'), right: tok('b') });
        expect(m).toMatchTranscript(['left/a', 'right/b']);
        expect(m).toMatchTranscript(['right/b', 'left/a']);
    });

    it('rejects tokens without left/ or right/ prefix', () => {
        const m = product({ left: tok('a'), right: tok('b') });
        expect(m).not.toMatchTranscript(['a', 'right/b']);
        expect(m).not.toMatchTranscript(['left/a', 'b']);
    });

    it('validates product of sequence machines', () => {
        const left = sequence(tok('x'), tok('y'));
        const right = sequence(tok('a'), tok('b'));
        const m = product({ left, right });
        expect(m).toMatchTranscript(['left/x', 'right/a', 'left/y', 'right/b']);
    });

    it('rejects when left or right stream is invalid', () => {
        const m = product({ left: tok('a'), right: tok('b') });
        expect(m).not.toMatchTranscript(['left/wrong', 'right/b']);
        expect(m).not.toMatchTranscript(['left/a', 'right/wrong']);
    });

    it('accepts empty transcript when both sides accept empty', () => {
        const m = product({
            left: { kind: 'sequence', inner: [] },
            right: { kind: 'sequence', inner: [] },
        });
        expect(m).toMatchTranscript([]);
    });

    it('sequence(A, product(B, C), D) leaves remainder for D', () => {
        const m = sequence(
            tok('a'),
            product({ left: tok('b'), right: tok('c') }),
            tok('d'),
        );
        expect(m).toMatchTranscript(['a', 'left/b', 'right/c', 'd']);
        expect(m).not.toMatchTranscript(['a', 'left/b', 'right/c']);
    });

    it('sequence(product(A, B), product(C, D), E) two products in a row', () => {
        const m = sequence(
            product({ left: tok('a'), right: tok('b') }),
            product({ left: tok('c'), right: tok('d') }),
            tok('e'),
        );
        expect(m).toMatchTranscript(['left/a', 'right/b', 'left/c', 'right/d', 'e']);
        expect(m).not.toMatchTranscript(['left/a', 'right/b', 'left/c', 'right/d']);
    });
});

function sequence(...machines: MachineType[]): MachineType {    
    return {
        kind: 'sequence',
        inner: machines,
    };
}

function choice(inner: Record<string, MachineType>): MachineType {
    return {
        kind: 'choice',
        inner,
    };
}

function emit(t: string): MachineType {
    return {
        kind: 'emit',
        token: t,
    };
}

function receive(t: string): MachineType {
    return choice({ [t]: sequence() });
}

function loop(f: (self: MachineType) => MachineType): MachineType {
    return {
        kind: 'loop',
        inner: f,
    };
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
            'correct': sequence(onCorrect),
            'incorrect': sequence(self),
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
            'enterDigit', 'enterDigit', 'enterDigit', 'enterDigit',
            'correct', 'pull', 'doorOpen',
        ]);
    });

    it('accepts four digits then incorrect then retry and succeed', () => {
        expect(secureDoor).toMatchTranscript([
            'enterDigit', 'enterDigit', 'enterDigit', 'enterDigit',
            'incorrect',
            'enterDigit', 'enterDigit', 'enterDigit', 'enterDigit',
            'correct', 'pull', 'doorOpen',
        ]);
    });

    it('accepts multiple wrong attempts then succeed', () => {
        expect(secureDoor).toMatchTranscript([
            'enterDigit', 'enterDigit', 'enterDigit', 'enterDigit', 'incorrect',
            'enterDigit', 'enterDigit', 'enterDigit', 'enterDigit', 'incorrect',
            'enterDigit', 'enterDigit', 'enterDigit', 'enterDigit',
            'correct', 'pull', 'doorOpen',
        ]);
    });

    it('rejects fewer than four digits before correct path', () => {
        expect(secureDoor).not.toMatchTranscript([
            'enterDigit', 'enterDigit', 'enterDigit',
            'correct', 'pull', 'doorOpen',
        ]);
    });

    it('rejects wrong order (e.g. doorOpen before pull)', () => {
        expect(secureDoor).not.toMatchTranscript([
            'enterDigit', 'enterDigit', 'enterDigit', 'enterDigit',
            'correct', 'doorOpen', 'pull',
        ]);
    });

    it('rejects correct without pull and doorOpen', () => {
        expect(secureDoor).not.toMatchTranscript([
            'enterDigit', 'enterDigit', 'enterDigit', 'enterDigit',
            'correct',
        ]);
    });

    it('rejects four digits only (no correct/incorrect outcome)', () => {
        expect(secureDoor).not.toMatchTranscript(['enterDigit', 'enterDigit', 'enterDigit', 'enterDigit']);
    });
});

const ref = loop((self) => choice({ 'end': sequence(), 'get': sequence(emit('result'), self) }));

function comparator(t: MachineType) : MachineType {
    return loop((self) =>
        choice({ 
            'cmp': sequence(
                product({
                    'left': t,
                    'right': t,
                }),
                emit('result'),
                self
            ),
            'end': sequence(),
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
        expect(comparator(ref)).toMatchTranscript(['cmp', 'left/end', 'right/end', 'result', 'end']);
    });

    it('accepts cmp then one get/result on left, end on right, then result', () => {
        expect(comparator(ref)).toMatchTranscript(['cmp', 'left/get', 'left/result', 'left/end', 'right/end', 'result', 'end']);
    });

    it('accepts cmp then one get/result on right, end on left, then result', () => {
        expect(comparator(ref)).toMatchTranscript(['cmp', 'right/get', 'right/result', 'left/end', 'right/end', 'result', 'end']);
    });

    it('accepts cmp then interleaved get/result on both sides then end then result', () => {
        expect(comparator(ref)).toMatchTranscript(['cmp', 'left/get', 'right/get', 'left/result', 'right/result', 'left/end', 'right/end', 'result', 'end']);
    });

    it('accepts cmp then multiple get/result on both sides then end then result', () => {
        expect(comparator(ref)).toMatchTranscript([
            'cmp',
            'left/get', 'left/result', 'right/get', 'right/result',
            'left/get', 'left/result', 'right/get', 'right/result',
            'left/end', 'right/end',
            'result',
            'end',
        ]);
    });

    it('rejects missing cmp', () => {
        expect(comparator(ref)).not.toMatchTranscript(['result']);
    });

    it('rejects missing final result', () => {
        expect(comparator(ref)).not.toMatchTranscript(['cmp']);
    });

    it('rejects incomplete ref stream (get without result)', () => {
        expect(comparator(ref)).not.toMatchTranscript(['cmp', 'left/get', 'result']);
    });

    it('rejects wrong channel prefix', () => {
        expect(comparator(ref)).not.toMatchTranscript(['cmp', 'other/get', 'result']);
    });
});

function lexCompare(t0: MachineType, t1: MachineType) : MachineType {
    return product({
        cmp: comparator(pair(t0, t1)),
        t0_cmp: comparator(t0),
        t1_cmp: comparator(t1),
    });
}

describe('lexCompare', () => {
    it('accepts cmp then end on both refs then result', () => {
        // This transcript is invalid: cmp channel gets [cmp, end] but comparator expects product then result before end
        expect(lexCompare(ref, ref)).toMatchTranscript([
            'cmp/cmp',
            't0_cmp/cmp',
            't0_cmp/left/get',
            'cmp/left/t0/get',
            'cmp/left/t0/result',
            't0_cmp/left/result',
            't0_cmp/left/end',
            
            't0_cmp/right/get',
            'cmp/right/t0/get',
            'cmp/right/t0/result',
            't0_cmp/right/result',
            't0_cmp/right/end',

            'cmp/left/t0/end',
            't0_cmp/result',
            't0_cmp/end',
            't1_cmp/end',
            'cmp/left/t1/end',
            'cmp/right/t0/end',
            'cmp/right/t1/end',
            'cmp/result',
            // 't1_cmp/end',
            'cmp/end',
        ]);
    });
});
