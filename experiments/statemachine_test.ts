import { assert } from "console";
import path from "path";

declare global {
    namespace jest {
        interface Matchers<R> {
            toMatchTranscript(transcript: string[]): R;
        }
    }
}

// type MachineImpl = {
//     kind: 'receive',
// } | {
//     kind: 'emit',
// } | {
//     kind: 'choice',
//     choices: Record<string, MachineImpl>
// }

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

// type MachineImplState = {
//     kind: 'receive' | 'emit',
// } | {
//     kind: 'choice',
//     choices: Record<string, MachineImplState>
// };

// function invalidMachineType(m: never): never {
//     throw new Error('Invalid machine type: ' + JSON.stringify(m));
// }

// function liveMachine(m: MachineImpl) : Machine<MachineImplState, string, string> {
//     return {
//         start(): MachineImplState {
//             if (m.kind === 'receive') {
//                 return {kind: 'receive'};
//             }
//             if (m.kind === 'emit') {
//                 return {kind: 'emit'};
//             }
//             if (m.kind === 'choice') {
//                 return {kind: 'choice', choices: Object.fromEntries(Object.keys(m.choices).map(k => [k, liveMachine(m.choices[k]).start()]))};
//             }
//             invalidMachineType(m);
//         },
//         readyForInput(s: MachineImplState): string[] {
//             if (m.kind === 'receive') {
//                 return ['.'];
//             }
//             if (m.kind === 'emit') {
//                 return [];
//             }
//             if (m.kind === 'choice') {
//                 if(s.kind !== 'choice') {
//                     throw new Error('Expected choice state, got ' + JSON.stringify(s));
//                 }
//                 const result: string[] = [];
//                 for (const choice of Object.keys(m.choices)) {
//                     for (const readySubpath of liveMachine(m.choices[choice]).readyForInput(s.choices[choice])) {
//                         result.push(path.join(choice, readySubpath));
//                     }
//                 }
//                 return result;
//             }
//             invalidMachineType(m);
//         },
//         sendInput (s, channel, data)  {
//             if (m.kind === 'receive') {
//                 if (s.kind !== 'receive') {
//                     throw new Error('Expected receive state, got ' + JSON.stringify(s));
//                 }
//                 return {kind: 'receive'};
//             }
//             if (m.kind === 'emit') {
//             invalidMachineType(m);
//         },
//     };
// }


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
// class MachineHelper {
//     private state: any;
//     constructor(private machine: Machine<any, any, any>) {
//         this.state = machine.start();
//     }

//     advance(channel: string, data: any): { channel: string, data: any } {
//         // Check if machine is ready for input on this channel
//         const readyChannels = this.machine.readyForInput(this.state);
//         if (readyChannels.includes(channel)) {
//             // Machine accepts input, send it
//             this.state = this.machine.sendInput(this.state, channel, data);
//         }

//         // Wait for output to be available on any channel
//         let availableOutputs = this.machine.hasOutput(this.state);
//         while (availableOutputs.length === 0) {
//             const [newState, advanced] = this.machine.advance(this.state);
//             if (!advanced) {
//                 throw new Error('Machine did not advance and no output available');
//             }
//             this.state = newState;
//             availableOutputs = this.machine.hasOutput(this.state);
//         }

//         // Get output from the first available channel
//         const outputChannel = availableOutputs[0];
//         const [newerState, output] = this.machine.getOutput(this.state, outputChannel);
//         this.state = newerState;

//         // Return channel and data separately
//         return {
//             channel: outputChannel,
//             data: output
//         };
//     }
//     readyForInput(): string[] {
//         return this.machine.readyForInput(this.state);
//     }
//     sendInput(channel: string, data: any) {
//         this.state = this.machine.sendInput(this.state, channel, data);
//     }

//     hasOutput(): string[] {
//         return this.machine.hasOutput(this.state);
//     }

//     getOutput(channel: string): any {
//         const [newState, output] = this.machine.getOutput(this.state, channel);
//         this.state = newState;
//         return output;
//     }
// }

// // Custom Jest matcher for MachineHelper
// expect.extend({
//     toAdvanceTo(received: MachineHelper, inputChannel: string, inputData: any, expectedChannel: string, expectedData: any) {
//         const actualOutput = received.advance(inputChannel, inputData);
//         const expectedOutput = { channel: expectedChannel, data: expectedData };
//         const pass = this.equals(actualOutput, expectedOutput);

//         if (pass) {
//             return {
//                 message: () => `Expected machine not to advance to ${this.utils.printExpected(expectedOutput)}`,
//                 pass: true,
//             };
//         } else {
//             return {
//                 message: () =>
//                     `Expected machine to advance to:\n` +
//                     `  ${this.utils.printExpected(expectedOutput)}\n` +
//                     `Received:\n` +
//                     `  ${this.utils.printReceived(actualOutput)}\n` +
//                     `Input was:\n` +
//                     `  channel: ${this.utils.printReceived(inputChannel)}, data: ${this.utils.printReceived(inputData)}`,
//                 pass: false,
//             };
//         }
//     },
// });

// // TypeScript declarations for the custom matcher
// declare global {
//     namespace jest {
//         interface Matchers<R> {
//             toAdvanceTo(inputChannel: string, inputData: any, expectedChannel: string, expectedData: any): R;
//         }
//     }
// }

// export { };

type Machine<S, I, O> = {
    start(): S;
    readyForInput(s: S): string[];
    sendInput(s: S, channel: string, data: I): S;
    hasOutput(s: S): string[];
    getOutput(s: S, channel: string): [S, O];
    advance(s: S): [S, boolean];
}

// // Test helper: runs a machine through a list of inputs and asserts the outputs match
// function runMachine<S, I, O>(machine: Machine<S, I, O>, ioPairs: Array<{ inputs: Array<{ channel: string, data: any }>, outputs: Array<{ channel: string, data: any }> }>): void {
//     let state = machine.start();
//     for (let i = 0; i < ioPairs.length; i++) {
//         const { inputs, outputs } = ioPairs[i];
//         // TODO
//     }
// }

// function devnull<S, I, O>(): Machine<S, I, O> {
//     return {
//         start(): any {
//             return null;
//         },
//         readyForInput(s: any): string[] {
//             return [""];
//         },
//         sendInput(s: any, channel: string, data: any): any {
//             return null;
//         },
//         hasOutput(s: any): string[] {
//             return [];
//         },
//         getOutput(s: any): [any, any] {
//             throw new Error('Invalid state: ' + s);
//         },
//         advance(s: any): [any, boolean] {
//             return [s, false];
//         },
//     }
// }

// function constant(data: any): Machine<any, any, any> {
//     return {
//         start(): any {
//             return null;
//         },
//         readyForInput(s: any): string[] {
//             return [];
//         },
//         sendInput(s: any, channel: string, data: any): any {
//             throw new Error('Invalid state: ' + s);
//         },
//         hasOutput(s: any): string[] {
//             return [""];
//         },
//         getOutput(s: any, channel: string): [any, any] {
//             if (channel !== "") {
//                 throw new Error('Invalid channel: ' + channel);
//             }
//             return [null, data];
//         },
//         advance(s: any): [any, boolean] {
//             return [s, false];
//         },
//     }
// }

// // describe('constant', () => {
// //     it('should handle multiple inputs correctly', () => {
// //         const helper = new MachineHelper(constant('data'));
// //         expect(helper).toAdvanceTo(
// //             { channel: '', data: 'input1', action: '' },
// //             { channel: 'break/result', data: 'data', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: 'input2', action: '' },
// //             { channel: 'break/result', data: 'data', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: 'input3', action: '' },
// //             { channel: 'break/result', data: 'data', action: '' }
// //         );
// //     });
// // });

// function composeSingle(m1: Machine<any, any, any>, m2: Machine<any, any, any>): Machine<any, any, any> {
//     const paired = renameChannels(product(m1, m2),
//         { 'public': 'left', 'private': 'right' },
//         { 'left': 'private', 'right': 'public' });
//     return loop(paired);
// }

// function compose(...machines: Machine<any, any, any>[]): Machine<any, any, any> {
//     if (machines.length === 0) {
//         throw new Error('compose requires at least one machine');
//     }
//     if (machines.length === 1) {
//         return machines[0];
//     }
//     let result = machines[0];
//     for (let i = 1; i < machines.length; i++) {
//         result = composeSingle(result, machines[i]);
//     }
//     return result;
// }

// describe('compose', () => {
//     it('should compose two func machines in sequence', () => {
//         const f1 = func((x: number) => x * 2);
//         const f2 = func((x: number) => x + 1);
//         const composed = compose(f1, f2);
//         const helper = new MachineHelper(composed);
//         expect(helper).toAdvanceTo('', 5, '', 11);
//     });

//     it('should compose three func machines in sequence', () => {
//         const f1 = func((x: number) => x * 2);
//         const f2 = func((x: number) => x + 1);
//         const f3 = func((x: number) => x * 3);
//         const composed = compose(f1, f2, f3);
//         const helper = new MachineHelper(composed);
//         expect(helper).toAdvanceTo('', 5, '', 33);
//     });

//     it('should handle string transformations in sequence', () => {
//         const f1 = func((s: string) => s.toUpperCase());
//         const f2 = func((s: string) => s + '!');
//         const composed = compose(f1, f2);
//         const helper = new MachineHelper(composed);
//         expect(helper).toAdvanceTo('', 'hello', '', 'HELLO!');
//     });

//     it('should handle type transformations through composition', () => {
//         const f1 = func((x: number) => x.toString());
//         const f2 = func((s: string) => s.length);
//         const composed = compose(f1, f2);
//         const helper = new MachineHelper(composed);
//         expect(helper).toAdvanceTo('', 12345, '', 5);
//     });

//     it('should handle single machine composition', () => {
//         const f1 = func((x: number) => x * 2);
//         const composed = compose(f1);
//         const helper = new MachineHelper(composed);
//         expect(helper).toAdvanceTo('', 5, '', 10);
//     });

//     it('should handle array transformations through composition', () => {
//         const f1 = func((arr: number[]) => arr.length);
//         const f2 = func((n: number) => n * 2);
//         const composed = compose(f1, f2);
//         const helper = new MachineHelper(composed);
//         expect(helper).toAdvanceTo('', [1, 2, 3, 4, 5], '', 10);
//     });
// });

// // Runs a until it is terminal, then runs the matching b from b_map.
// // function sequenceSingle(a: Machine, b: Machine): Machine {
// //     return {
// //         start(): [string, any] {
// //             return ['a', a.start()];
// //         },
// //         advance([state, s]: [string, any], i: Input): [any, Output] {
// //             if (state === 'a') {
// //                 const [new_s, o] = a.advance(s, i);
// //                 if (o.channel.startsWith('continue/') || o.channel.startsWith('yield/')) {
// //                     return [['a', new_s], { channel: o.channel, data: o.data, action: o.action }];
// //                 }
// //                 if (o.channel.startsWith('break/')) {
// //                     return [['b', b.start()], { channel: 'continue/' + o.channel.substring('break/'.length), data: o.data, action: o.action }];
// //                 }
// //                 throw new Error('Invalid channel: ' + o.channel);
// //             }
// //             if (state === 'b') {
// //                 const [new_s, o] = b.advance(s, i);
// //                 if (o.channel.startsWith('continue/') || o.channel.startsWith('yield/')) {
// //                     return [['b', new_s], { channel: o.channel, data: o.data, action: o.action }];
// //                 }
// //                 if (o.channel.startsWith('break/')) {
// //                     return [['end', null], { channel: o.channel, data: o.data, action: o.action }];
// //                 }
// //                 throw new Error('Invalid channel: ' + o.channel);
// //             }
// //             throw new Error('Invalid state: ' + state);
// //         },
// //     }
// // }

// // function sequence(...machines: Machine[]): Machine {
// //     if (machines.length === 0) {
// //         throw new Error('sequence requires at least one machine');
// //     }
// //     if (machines.length === 1) {
// //         return machines[0];
// //     }
// //     let result = machines[0];
// //     for (let i = 1; i < machines.length; i++) {
// //         result = sequenceSingle(result, machines[i]);
// //     }
// //     return result;
// // }

// // describe('sequence', () => {
// //     it('should start in A phase and then B phase', () => {
// //         const helper = new MachineHelper(sequenceSingle(constant('data1'), constant('data2')));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: 'ignored1', action: '' },
// //             { channel: 'continue/result', data: 'data1', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: 'ignored2', action: '' },
// //             { channel: 'break/result', data: 'data2', action: '' }
// //         );
// //     });
// // });

// type FuncState<O> = {
//     kind: 'start';
// } | {
//     kind: 'stored';
//     data: O;
// } | { 
//     kind: 'done';
// }

// function func<I, O>(f: (input: I) => O): Machine<FuncState<O>, I, O> {
//     return {
//         start(): FuncState<O> {
//             return { kind: 'start' };
//         },
//         readyForInput(s: FuncState<O>): string[] {
//             if (s.kind === 'start') {
//                 return [""];
//             }
//             return [];
//         },
//         sendInput(s: FuncState<O>, channel: string, data: I): FuncState<O> {
//             if (s.kind === 'start') {
//                 if (channel !== "") {
//                     throw new Error('Invalid channel: ' + channel);
//                 }
//                 return { kind: 'stored', data: f(data) };
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//         hasOutput(s: FuncState<O>): string[] {
//             if (s.kind === 'stored') {
//                 return [""];
//             }
//             return [];
//         },
//         getOutput(s: FuncState<O>, channel: string): [FuncState<O>, O] {
//             if (s.kind === 'stored') {
//                 return [{ kind: 'done' }, s.data];
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//         advance(s: any): [any, boolean] {
//             return [s, false];
//         },
//     }
// }

// describe('func', () => {
//     it('should transform input using the provided function', () => {
//         const helper = new MachineHelper(func((x: number) => x * 2));
//         expect(helper).toAdvanceTo('', 5, '', 10);
//     });

//     it('should handle string transformations', () => {
//         const helper = new MachineHelper(func((s: string) => s.toUpperCase()));
//         expect(helper).toAdvanceTo('', 'hello', '', 'HELLO');
//     });

//     it('should handle array transformations', () => {
//         const helper = new MachineHelper(func((arr: number[]) => arr.length));
//         expect(helper).toAdvanceTo('', [1, 2, 3, 4], '', 4);
//     });

//     it('should handle object transformations', () => {
//         const helper = new MachineHelper(func((obj: { x: number, y: number }) => obj.x + obj.y));
//         expect(helper).toAdvanceTo('', { x: 3, y: 4 }, '', 7);
//     });

//     it('should process input and return transformed output', () => {
//         const helper = new MachineHelper(func((x: number) => x + 1));
//         expect(helper).toAdvanceTo('', 1, '', 2);
//     });

//     it('should handle functions that return complex values', () => {
//         const helper = new MachineHelper(func((x: number) => ({ doubled: x * 2, squared: x * x })));
//         expect(helper).toAdvanceTo('', 5, '', { doubled: 10, squared: 25 });
//     });

//     it('should handle functions that return arrays', () => {
//         const helper = new MachineHelper(func((x: number) => [x, x * 2, x * 3]));
//         expect(helper).toAdvanceTo('', 3, '', [3, 6, 9]);
//     });
// });

// // function yld(channel: string): Machine {
// //     return {
// //         start(): any {
// //             return 'start';
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             if (s === 'start') {
// //                 if (i.channel !== "result") {
// //                     throw new Error('Invalid channel: ' + i.channel);
// //                 }
// //                 return ['awaiting', { channel: 'yield/' + channel, data: i.data, action: '' }];
// //             }
// //             if (s === 'awaiting') {
// //                 if (i.channel !== channel) {
// //                     throw new Error('Invalid channel: ' + i.channel);
// //                 }
// //                 return ['end', { channel: "break/result", data: i.data, action: '' }];
// //             }
// //             throw new Error('Invalid state: ' + s);
// //         },
// //     }
// // }

// // function brk(): Machine {
// //     return {
// //         start(): any {
// //             return 'start';
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             if (i.channel !== 'result') {
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             return ['end', { channel: 'break/result', data: i.data, action: '' }];
// //         },
// //     }
// // }

// // function stash(inner: Machine): Machine {
// //     return {
// //         start(): any {
// //             return { kind: 'start' };
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             if (s.kind === 'start') {
// //                 if (i.channel !== 'result') {
// //                     throw new Error('Invalid channel: ' + i.channel);
// //                 }
// //                 let [new_inner, output] = inner.advance(inner.start(), { channel: 'result', data: i.data[1], action: '' });

// //                 if (output.channel.startsWith('break/')) {
// //                     return [{ kind: 'end' }, { channel: output.channel, data: [i.data[0], output.data], action: output.action }];
// //                 }
// //                 return [{ kind: 'running', stashed: i.data[0], inner: new_inner }, { channel: output.channel, data: output.data, action: output.action }];
// //             }
// //             if (s.kind === 'running') {
// //                 let [new_inner, output] = inner.advance(s.inner, i);
// //                 if (output.channel.startsWith('break/')) {
// //                     return [{ kind: 'end' }, { channel: output.channel, data: [s.stashed, output.data], action: output.action }];
// //                 }
// //                 return [{ kind: 'running', stashed: s.stashed, inner: new_inner }, { channel: output.channel, data: output.data, action: output.action }];
// //             }
// //             throw new Error('Invalid state: ' + s);
// //         },
// //     }
// // }

// // function pipeline(machine: Machine): Machine {
// //     return {
// //         start(): any {
// //             return machine.start();
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             while (true) {
// //                 const [new_s, output] = machine.advance(s, i);
// //                 if (output.channel !== 'continue/result') {
// //                     return [new_s, output];
// //                 }
// //                 s = new_s;
// //                 i = { channel: 'result', data: output.data, action: output.action };
// //             }
// //             return [s, i]
// //         },
// //     }
// // }

// // describe('yld', () => {
// //     it('func with yld', () => {
// //         const f = func((x: any) => [x + 1, 'hello world']);
// //         const y = yld('channel');
// //         const g = func(([x, y]: [number, string]) => '' + y + "/" + x);
// //         const helper = new MachineHelper(sequence(f, stash(y), g, brk()));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: 4, action: '' },
// //             { channel: 'continue/result', data: [5, 'hello world'], action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: [5, 'hello world'], action: '' },
// //             { channel: 'yield/channel', data: 'hello world', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'channel', data: 'my guy', action: '' },
// //             { channel: 'continue/result', data: [5, 'my guy'], action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: [5, 'my guy'], action: '' },
// //             { channel: 'continue/result', data: 'my guy/5', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: 'my guy/5', action: '' },
// //             { channel: 'break/result', data: 'my guy/5', action: '' }
// //         );
// //     });

// //     it('func with yld pipelined', () => {
// //         const f = func((x: any) => [x + 1, 'hello world']);
// //         const y = yld('channel');
// //         const g = func(([x, y]: [number, string]) => '' + y + "/" + x);
// //         const helper = new MachineHelper(loop(sequence(f, stash(y), g, brk())));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: 4, action: '' },
// //             { channel: 'channel', data: 'hello world', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'channel', data: 'my guy', action: '' },
// //             { channel: 'result', data: 'my guy/5', action: '' }
// //         );
// //     });
// // });

// // function array(size: number): Machine {
// //     return {
// //         start(): any {
// //             return { kind: 'ready', arr: Array(size).fill(null) };
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             if (s.kind === 'ready') {
// //                 const arr = s.arr;
// //                 if (i.channel === "set") {
// //                     const [idx, value] = i.data;
// //                     if (idx < 0 || idx >= size) {
// //                         return [arr, { channel: 'err', data: 'invalid index: ' + idx, action: '' }];
// //                     }
// //                     arr[idx] = value;
// //                     return [{ kind: 'ready', arr: arr }, { channel: 'result', data: null, action: '' }];
// //                 }
// //                 if (i.channel === "take") {
// //                     const idx = i.data;
// //                     if (idx < 0 || idx >= size) {
// //                         return [{ kind: 'ready', arr: arr }, { channel: 'err', data: 'invalid index: ' + idx, action: '' }];
// //                     }
// //                     return [{ kind: 'incomplete', arr: arr, idx: idx }, { channel: 'result', data: arr[idx], action: '' }];
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             if (s.kind === 'incomplete') {
// //                 const arr = s.arr;
// //                 const idx = s.idx;
// //                 if (i.channel === "set") {
// //                     const [idx2, value] = i.data;
// //                     if (idx2 !== idx) {
// //                         return [s, { channel: 'err', data: 'invalid index: ' + idx2, action: '' }];
// //                     }
// //                     arr[idx] = value;
// //                     return [{ kind: 'ready', arr: arr }, { channel: 'result', data: null, action: '' }];
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             throw new Error('Invalid state: ' + s);
// //         },
// //     }
// // }

// // describe('array', () => {
// //     it('should set values at valid indices', () => {
// //         const helper = new MachineHelper(array(3));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [0, 'first'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [1, 'second'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [2, 'third'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //     });

// //     it('should take values at valid indices', () => {
// //         const helper = new MachineHelper(array(3));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [0, 'value0'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [1, 'value1'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'take', data: 0, action: '' },
// //             { channel: 'result', data: 'value0', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [0, 'value0'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'take', data: 1, action: '' },
// //             { channel: 'result', data: 'value1', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [1, 'value1'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //     });

// //     it('should return null for uninitialized indices', () => {
// //         const helper = new MachineHelper(array(3));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'take', data: 0, action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [0, null], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'take', data: 1, action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [1, null], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //     });

// //     it('should handle take-then-set pattern in incomplete state', () => {
// //         const helper = new MachineHelper(array(3));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [0, 'initial'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'take', data: 0, action: '' },
// //             { channel: 'result', data: 'initial', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [0, 'updated'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'take', data: 0, action: '' },
// //             { channel: 'result', data: 'updated', action: '' }
// //         );
// //     });

// //     it('should error on invalid index for set', () => {
// //         const arr = array(3);
// //         expect(() => {
// //             const [state, output] = arr.advance(arr.start(), { channel: 'set', data: [5, 'value'], action: '' });
// //             if (output.channel === 'err') {
// //                 throw new Error(output.data);
// //             }
// //         }).toThrow('invalid index: 5');
// //     });

// //     it('should error on negative index for set', () => {
// //         const arr = array(3);
// //         expect(() => {
// //             const [state, output] = arr.advance(arr.start(), { channel: 'set', data: [-1, 'value'], action: '' });
// //             if (output.channel === 'err') {
// //                 throw new Error(output.data);
// //             }
// //         }).toThrow('invalid index: -1');
// //     });

// //     it('should error on invalid index for take', () => {
// //         const arr = array(3);
// //         expect(() => {
// //             const [state, output] = arr.advance(arr.start(), { channel: 'take', data: 10, action: '' });
// //             if (output.channel === 'err') {
// //                 throw new Error(output.data);
// //             }
// //         }).toThrow('invalid index: 10');
// //     });

// //     it('should error on wrong index in incomplete state', () => {
// //         const arr = array(3);
// //         let state = arr.start();
// //         const [state1, output1] = arr.advance(state, { channel: 'take', data: 0, action: '' });
// //         expect(() => {
// //             const [state2, output2] = arr.advance(state1, { channel: 'set', data: [1, 'wrong'], action: '' });
// //             if (output2.channel === 'err') {
// //                 throw new Error(output2.data);
// //             }
// //         }).toThrow('invalid index: 1');
// //     });

// //     it('should handle multiple operations correctly', () => {
// //         const helper = new MachineHelper(array(5));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [0, 'a'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [1, 'b'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [2, 'c'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'take', data: 0, action: '' },
// //             { channel: 'result', data: 'a', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [0, 'A'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'take', data: 1, action: '' },
// //             { channel: 'result', data: 'b', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [1, 'B'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'take', data: 2, action: '' },
// //             { channel: 'result', data: 'c', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: [2, 'C'], action: '' },
// //             { channel: 'result', data: null, action: '' }
// //         );
// //     });
// // });

// // function advancePrimitive(s: any, i: Input): [any, Output] {
// //     const channel = i.channel.split('/');
// //     if (channel[0] === 'set') {
// //         return [i.data, { channel: 'set', data: null, action: '' }];
// //     }
// //     if (channel[0] === 'copy') {
// //         return [s, { channel: 'copy', data: s, action: '' }];
// //     }
// //     if (channel[0] === 'element') {
// //         if (!Array.isArray(s)) {
// //             return [s, { channel: 'err', data: 'not an array', action: '' }];
// //         }
// //         const idx = parseInt(channel[1]);
// //         if (idx < 0 || idx >= s.length) {
// //             return [s, { channel: 'err', data: 'invalid index: ' + idx, action: '' }];
// //         }
// //         const subchannel = channel.slice(2).join('/');
// //         const [new_s, output] = advancePrimitive(s[idx], { channel: subchannel, data: i.data, action: i.action });
// //         s[idx] = new_s;
// //         return [s, { channel: 'element/' + idx + '/' + output.channel, data: output.data, action: output.action }];
// //     }
// //     throw new Error('Invalid channel: ' + i.channel);
// // }

// // function primitive(): Machine {
// //     return {
// //         start(): any {
// //             return null;
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             return advancePrimitive(s, i);
// //         },
// //     }
// // }

// // function name2(): Machine {
// //     return {
// //         start(): any {
// //             return { kind: 'start' };
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             const channel = i.channel.split('/');
// //             if (s.kind === 'start') {
// //                 if (channel[0] === 'first') {
// //                     const subchannel = channel.slice(1).join('/');
// //                     return [{ kind: 'awaitingFirst' }, { channel: 'inner/left/' + subchannel, data: i.data, action: i.action }];
// //                 }
// //                 if (channel[0] === 'last') {
// //                     const subchannel = channel.slice(1).join('/');
// //                     return [{ kind: 'awaitingLast' }, { channel: 'inner/right/' + subchannel, data: i.data, action: i.action }];
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             if (s.kind === 'awaitingFirst') {
// //                 if (i.channel === 'inner/left/result') {
// //                     return [{ kind: 'start' }, { channel: 'first/result', data: i.data, action: i.action }];
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             if (s.kind === 'awaitingLast') {
// //                 if (i.channel === 'inner/right/result') {
// //                     return [{ kind: 'start' }, { channel: 'last/result', data: i.data, action: i.action }];
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             throw new Error('Invalid state: ' + s);
// //         },
// //     }
// // }

// // function name(): Machine {
// //     return renameChannels({
// //         'inner/left': 'first',
// //         'inner/right': 'last',
// //         'first': 'inner/left',
// //         'last': 'inner/right',
// //     });
// // }

// function product<S1, I1, O1, S2, I2, O2>(m1: Machine<S1, I1, O1>, m2: Machine<S2, I2, O2>): Machine<[S1, S2], I1 | I2, O1 | O2> {
//     return {
//         start(): [S1, S2] {
//             return [m1.start(), m2.start()];
//         },
//         readyForInput([s1, s2]: [S1, S2]): string[] {
//             return [...m1.readyForInput(s1).map(s => 'left/' + s), ...m2.readyForInput(s2).map(s => 'right/' + s)];
//         },
//         sendInput([s1, s2]: [S1, S2], channel: string, data: I1 | I2): [S1, S2] {
//             if (channel.startsWith('left/')) {
//                 return [m1.sendInput(s1, channel.slice(5), data as I1), s2];
//             }
//             if (channel.startsWith('right/')) {
//                 return [s1, m2.sendInput(s2, channel.slice(6), data as I2)];
//             }
//             throw new Error('Invalid channel: ' + channel);
//         },
//         hasOutput([s1, s2]: [S1, S2]): string[] {
//             return [...m1.hasOutput(s1).map(s => 'left/' + s), ...m2.hasOutput(s2).map(s => 'right/' + s)];
//         },
//         getOutput([s1, s2]: [S1, S2], channel: string): [[S1, S2], O1 | O2] {
//             if (channel.startsWith('left/')) {
//                 const [new_s1, output] = m1.getOutput(s1, channel.slice(5));
//                 return [[new_s1, s2], output];
//             }
//             if (channel.startsWith('right/')) {
//                 const [new_s2, output] = m2.getOutput(s2, channel.slice(6));
//                 return [[s1, new_s2], output];
//             }
//             throw new Error('Invalid channel: ' + channel);
//         },
//         advance([s1, s2]: [S1, S2]): [[S1, S2], boolean] {
//             const [new_s1, s1_advanced] = m1.advance(s1);
//             const [new_s2, s2_advanced] = m2.advance(s2);
//             return [[new_s1, new_s2], s1_advanced || s2_advanced];
//         },
//     }
// }

// // function nameBindPrimitive(inner: Machine): Machine {
// //     return {
// //         start(): any {
// //             return { primitive: inner.start(), name: name().start() };
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             let [name_s, name_output] = name().advance(s.name, i);
// //             let channel = name_output.channel.split('/');
// //             let primitive_s = s.primitive;
// //             while (channel[0] === 'inner') {
// //                 const subchannel = channel.slice(1).join('/');
// //                 const [new_primitive_s, primitive_output] = inner.advance(primitive_s, { channel: subchannel, data: name_output.data, action: name_output.action });
// //                 primitive_s = new_primitive_s;
// //                 [name_s, name_output] = name().advance(name_s, { channel: 'inner/' + primitive_output.channel, data: primitive_output.data, action: primitive_output.action });
// //                 channel = name_output.channel.split('/');
// //             }
// //             if (channel[0] === 'result' || channel[0] === 'first' || channel[0] === 'second') {
// //                 return [{ primitive: primitive_s, name: name_s }, { channel: name_output.channel, data: name_output.data, action: name_output.action }];
// //             }
// //             throw new Error('Invalid channel: ' + name_output.channel);
// //         },
// //     }
// // }

// // function renameChannel(old_channel: string, new_channel: string): Machine {
// //     return {
// //         start(): any {
// //             return null;
// //         },
// //         advance(s: null, i: Input): [any, Output] {
// //             const channel = i.channel.split('/');
// //             const old_channel_parts = old_channel.split('/');
// //             const new_channel_parts = new_channel.split('/');
// //             // Check if the prefix of channel matches old_channel
// //             if (channel.length >= old_channel_parts.length) {
// //                 let matches = true;
// //                 for (let i = 0; i < old_channel_parts.length; i++) {
// //                     if (channel[i] !== old_channel_parts[i]) {
// //                         matches = false;
// //                         break;
// //                     }
// //                 }
// //                 if (matches) {
// //                     return [null, { channel: [...new_channel_parts, ...channel.slice(old_channel_parts.length)].join('/'), data: i.data, action: i.action }];
// //                 }
// //             }
// //             return [null, { channel: i.channel, data: i.data, action: i.action }];
// //         },
// //     }
// // }

// function renameChannel(channel: string, renames: Record<string, string>): string {
//     const channelParts = channel.split('/');
//     // Find the longest matching prefix
//     let bestMatch: { oldParts: string[], newParts: string[] } | null = null;
//     let bestLength = -1;

//     for (const [old_channel, new_channel] of Object.entries(renames)) {
//         const old_channel_parts = old_channel.split('/');
//         // Handle empty prefix: '' should match everything
//         const effectiveLength = (old_channel_parts.length === 1 && old_channel_parts[0] === '') ? 0 : old_channel_parts.length;

//         if (channelParts.length >= effectiveLength && effectiveLength > bestLength) {
//             let matches = true;
//             // Empty prefix always matches
//             if (effectiveLength > 0) {
//                 for (let j = 0; j < old_channel_parts.length; j++) {
//                     if (channelParts[j] !== old_channel_parts[j]) {
//                         matches = false;
//                         break;
//                     }
//                 }
//             }
//             if (matches) {
//                 bestMatch = { oldParts: old_channel_parts, newParts: new_channel.split('/') };
//                 bestLength = effectiveLength;
//             }
//         }
//     }

//     if (bestMatch) {
//         const remainingParts = channelParts.slice(bestLength);
//         // Handle empty new_channel: if newParts is [''] and there are remaining parts, just use remaining parts
//         if (bestMatch.newParts.length === 1 && bestMatch.newParts[0] === '' && remainingParts.length > 0) {
//             return remainingParts.join('/');
//         }
//         return [...bestMatch.newParts, ...remainingParts].join('/');
//     }
//     return channel;
// }

// function renameChannels(inner: Machine<any, any, any>, inputRenames: Record<string, string>, outputRenames: Record<string, string>): Machine<any, any, any> {
//     return {
//         start(): any {
//             return inner.start();
//         },
//         readyForInput(s: any): string[] {
//             const innerChannels = inner.readyForInput(s);
//             // Rename output channels back to input channels (reverse of input renames)
//             // We need to reverse the mapping: if input renames map "outer" -> "inner",
//             // then when inner says it's ready for "inner", we should say we're ready for "outer"
//             const reverseInputRenames: Record<string, string> = {};
//             for (const [oldChannel, newChannel] of Object.entries(inputRenames)) {
//                 reverseInputRenames[newChannel] = oldChannel;
//             }
//             return innerChannels.map(ch => renameChannel(ch, reverseInputRenames));
//         },
//         sendInput(s: any, channel: string, data: any): any {
//             // Rename input channel before sending to inner machine
//             const innerChannel = renameChannel(channel, inputRenames);
//             return inner.sendInput(s, innerChannel, data);
//         },
//         hasOutput(s: any): string[] {
//             const innerChannels = inner.hasOutput(s);
//             // Rename output channels
//             return innerChannels.map(ch => renameChannel(ch, outputRenames));
//         },
//         getOutput(s: any, channel: string): [any, any] {
//             // Rename output channel back to inner channel (reverse of output renames)
//             const reverseOutputRenames: Record<string, string> = {};
//             for (const [oldChannel, newChannel] of Object.entries(outputRenames)) {
//                 reverseOutputRenames[newChannel] = oldChannel;
//             }
//             const innerChannel = renameChannel(channel, reverseOutputRenames);
//             return inner.getOutput(s, innerChannel);
//         },
//         advance(s: any): [any, boolean] {
//             return inner.advance(s);
//         },
//     }
// }

// // describe('renameChannels', () => {
// //     it('should rename channels', () => {
// //         const helper = new MachineHelper(renameChannels({ 'inner/left': 'first', 'inner/right': 'last' }));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/set', data: 'a', action: '' },
// //             { channel: 'first/set', data: 'a', action: '' }
// //         );
// //     });
// //     it('should support empty prefix', () => {
// //         const helper = new MachineHelper(renameChannels({ '': 'first' }));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'set', data: 'a', action: '' },
// //             { channel: 'first/set', data: 'a', action: '' }
// //         );
// //     });
// //     it('should support renaming to empty value', () => {
// //         const helper = new MachineHelper(renameChannels({ 'first': '' }));
// //         expect(helper).toAdvanceTo(
// //             { channel: 'first/set', data: 'a', action: '' },
// //             { channel: 'set', data: 'a', action: '' }
// //         );
// //     });
// // });

// type LoopState<S, C> = {
//     kind: 'ready';
//     state: S;
// } | {
//     kind: 'looping';
//     state: S;
//     channel: string;
//     data: C;
// }

// function loop<S, I, O, C>(inner: Machine<S, I | C, O | C>): Machine<LoopState<S, C>, I, O> {
//     return {
//         start(): LoopState<S, C> {
//             return { kind: "ready", state: inner.start() };
//         },
//         readyForInput(s: LoopState<S, C>): string[] {
//             if (s.kind === 'ready') {
//                 const res: string[] = [];
//                 for (const channel of inner.readyForInput(s.state)) {
//                     if (channel.startsWith('public/')) {
//                         res.push(channel.slice('public/'.length));
//                     }
//                 }
//                 return res;
//             }
//             if (s.kind === 'looping') {
//                 return []
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//         sendInput(s: LoopState<S, C>, channel: string, data: any): LoopState<S, C> {
//             if (s.kind === 'ready') {
//                 return { kind: 'ready', state: inner.sendInput(s.state, 'public/' + channel, data) };
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//         hasOutput(s: LoopState<S, C>): string[] {
//             if (s.kind === 'ready') {
//                 const res = [];
//                 for (const channel of inner.hasOutput(s.state)) {
//                     if (channel.startsWith('public/')) {
//                         res.push(channel.slice('public/'.length));
//                     }
//                 }
//                 return res;
//             }
//             if (s.kind === 'looping') {
//                 return []
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//         getOutput(s: LoopState<S, C>, channel: string): [LoopState<S, C>, any] {
//             if (s.kind === 'ready') {
//                 const [new_s, output] = inner.getOutput(s.state, 'public/' + channel);
//                 return [{ kind: 'ready', state: new_s }, output];
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//         advance(s: LoopState<S, C>): [LoopState<S, C>, boolean] {
//             if (s.kind === 'ready') {
//                 const [new_s, inner_advanced] = inner.advance(s.state);
//                 if (inner_advanced) {
//                     return [{ kind: 'ready', state: new_s }, true];
//                 }
//                 const ready_outs = inner.hasOutput(new_s);
//                 for (const channel of ready_outs) {
//                     if (channel.startsWith('private/')) {
//                         const [newer_s, output] = inner.getOutput(new_s, channel);
//                         return [{ kind: 'looping', state: newer_s, channel: channel, data: output as C }, true];
//                     }
//                 }
//                 return [{ kind: 'ready', state: new_s }, false];
//             }
//             if (s.kind === 'looping') {
//                 if (inner.readyForInput(s.state).includes(s.channel)) {
//                     const new_s = inner.sendInput(s.state, s.channel, s.data);
//                     return [{ kind: 'ready', state: new_s }, true];
//                 }
//                 const [new_s, inner_advanced] = inner.advance(s.state);
//                 if (!inner_advanced) {
//                     throw new Error('Inner machine did not advance');
//                 }
//                 return [{ kind: 'looping', state: new_s, channel: s.channel, data: s.data }, true];
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//     }
// }

// // describe('name', () => {
// //     it('should allow accessing elements of the name unbound', () => {
// //         const helper = new MachineHelper(name());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'first/set', data: 'a', action: '' },
// //             { channel: 'inner/left/set', data: 'a', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/result', data: null, action: '' },
// //             { channel: 'first/result', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'first/copy', data: null, action: '' },
// //             { channel: 'inner/left/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/result', data: 'a', action: '' },
// //             { channel: 'first/result', data: 'a', action: '' }
// //         );
// //     });
// //     it('should allow accessing elements of the name unbound paired', () => {
// //         const pair = product(primitive(), primitive());
// //         const name_pair = compose(
// //             product(name(), pair),
// //             renameChannel('left/inner', 'continue/right'),
// //             renameChannel('right', 'continue/left/inner'),
// //             renameChannel('left/first', 'break/left/first'));
// //         const helper = new MachineHelper(name_pair);
// //         expect(helper).toAdvanceTo(
// //             { channel: 'left/first/set', data: 'a', action: '' },
// //             { channel: 'continue/right/left/set', data: 'a', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'right/left/set', data: 'a', action: '' },
// //             { channel: 'continue/left/inner/left/set', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'left/inner/left/set', data: null, action: '' },
// //             { channel: 'break/left/first/set', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'left/first/copy', data: null, action: '' },
// //             { channel: 'continue/right/left/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'right/left/copy', data: null, action: '' },
// //             { channel: 'continue/left/inner/left/copy', data: 'a', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'left/inner/left/result', data: 'a', action: '' },
// //             { channel: 'break/left/first/result', data: 'a', action: '' }
// //         );
// //     });
// //     it('should allow accessing elements of the name', () => {
// //         const pair = product(primitive(), primitive());
// //         const name_pair = compose(
// //             product(name(), pair),
// //             renameChannel('left/inner', 'continue/right'),
// //             renameChannel('right', 'continue/left/inner'),
// //             renameChannel('left/first', 'break/left/first'));
// //         const n = compose(
// //             renameChannel('first', 'left/first'),
// //             renameChannel('second', 'left/second'),
// //             loop(name_pair),
// //             renameChannel('left/first', 'first'),
// //             renameChannel('left/second', 'second'),
// //         );

// //         const helper = new MachineHelper(n);
// //         expect(helper).toAdvanceTo(
// //             { channel: 'first/set', data: 'a', action: '' },
// //             { channel: 'first/set', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'first/copy', data: null, action: '' },
// //             { channel: 'first/copy', data: 'a', action: '' }
// //         );
// //     });
// // });

// // function stringCompare(): Machine<any, any, any> {
// //     return {
// //         start(): any {
// //             return { kind: 'start' };
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             if (s.kind === 'start') {
// //                 if (i.channel === 'result') {
// //                     return [{ kind: 'awaitingLeft' }, { channel: 'inner/left/copy', data: null, action: '' }];
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             if (s.kind === 'awaitingLeft') {
// //                 if (i.channel === 'inner/left/copy') {
// //                     return [{ kind: 'awaitingRight', left: i.data }, { channel: 'inner/right/copy', data: null, action: '' }];
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             if (s.kind === 'awaitingRight') {
// //                 if (i.channel === 'inner/right/copy') {
// //                     function strCmp(left: string, right: string): '<' | '>' | '=' {
// //                         if (left < right) {
// //                             return '<';
// //                         }
// //                         if (left > right) {
// //                             return '>';
// //                         }
// //                         return '=';
// //                     }
// //                     return [{ kind: 'start' }, { channel: 'result', data: strCmp(s.left, i.data), action: '' }];
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             throw new Error('Invalid state: ' + s);
// //         },
// //     }
// // }

// // describe('stringCompare', () => {
// //     it('should compare strings and return less than', () => {
// //         const helper = new MachineHelper(stringCompare());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: null, action: '' },
// //             { channel: 'inner/left/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/copy', data: 'apple', action: '' },
// //             { channel: 'inner/right/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/right/copy', data: 'banana', action: '' },
// //             { channel: 'result', data: '<', action: '' }
// //         );
// //     });

// //     it('should compare strings and return greater than', () => {
// //         const helper = new MachineHelper(stringCompare());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: null, action: '' },
// //             { channel: 'inner/left/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/copy', data: 'zebra', action: '' },
// //             { channel: 'inner/right/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/right/copy', data: 'apple', action: '' },
// //             { channel: 'result', data: '>', action: '' }
// //         );
// //     });

// //     it('should compare strings and return equal', () => {
// //         const helper = new MachineHelper(stringCompare());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: null, action: '' },
// //             { channel: 'inner/left/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/copy', data: 'hello', action: '' },
// //             { channel: 'inner/right/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/right/copy', data: 'hello', action: '' },
// //             { channel: 'result', data: '=', action: '' }
// //         );
// //     });

// //     it('should handle multiple comparisons', () => {
// //         const helper = new MachineHelper(stringCompare());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: null, action: '' },
// //             { channel: 'inner/left/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/copy', data: 'a', action: '' },
// //             { channel: 'inner/right/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/right/copy', data: 'b', action: '' },
// //             { channel: 'result', data: '<', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'result', data: null, action: '' },
// //             { channel: 'inner/left/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/copy', data: 'x', action: '' },
// //             { channel: 'inner/right/copy', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/right/copy', data: 'y', action: '' },
// //             { channel: 'result', data: '<', action: '' }
// //         );
// //     });

// //     // it('should work with binding', () => {
// //     //     const testBody = loop(sequence(
// //     //         constant('a'),
// //     //         yld('pair/left/set'),
// //     //         constant('b'),
// //     //         yld('pair/right/set'),
// //     //         compose(
// //     //             renameChannels({
// //     //                 'pair': 'inner',
// //     //             }),
// //     //             stringCompare(),
// //     //             renameChannels({
// //     //                 'inner': 'yield/pair',
// //     //                 'result': 'break/result',
// //     //             }),
// //     //         )
// //     //     ));

// //     //     const dataPair = product(primitive(), primitive());
// //     //     const boundBody = compose(
// //     //         product(testBody, dataPair),
// //     //         renameChannels({
// //     //             'left/pair': 'continue/right',
// //     //             'right': 'continue/left/pair',
// //     //             'left/result': 'break/left/result',
// //     //         }),
// //     //     );
// //     //     const boundLoop = compose(renameChannels({ '': 'left' }), loop(boundBody), renameChannels({ 'left': '' }));
// //     //     const helper = new MachineHelper(boundLoop);
// //     //     expect(helper).toAdvanceTo(
// //     //         { channel: 'result', data: null, action: '' },
// //     //         { channel: 'result', data: '<', action: '' }
// //     //     );
// //     // });
// // });


// // function lexCompare(): Machine {
// //     return {
// //         start(): any {
// //             return { kind: 'start' };
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             if (s.kind === 'start') {
// //                 if (i.channel === 'cmp') {
// //                     return [{ kind: 'awaitingLeft' }, { channel: 'inner/left/cmp', data: null, action: '' }];
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             if (s.kind === 'awaitingLeft') {
// //                 if (i.channel === 'inner/left/result') {
// //                     if (i.data === '=') {
// //                         return [{ kind: 'awaitingRight' }, { channel: 'inner/right/cmp', data: null, action: '' }];
// //                     } else {
// //                         return [{ kind: 'start' }, { channel: 'result', data: i.data, action: '' }];
// //                     }
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             if (s.kind === 'awaitingRight') {
// //                 if (i.channel === 'inner/right/result') {
// //                     return [{ kind: 'start' }, { channel: 'result', data: i.data, action: '' }];
// //                 }
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             throw new Error('Invalid state: ' + s);
// //         },
// //     }
// // }

// // describe('lexCompare', () => {
// //     it('should return result immediately when left comparison is not equal', () => {
// //         const helper = new MachineHelper(lexCompare());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'cmp', data: null, action: '' },
// //             { channel: 'inner/left/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/result', data: '<', action: '' },
// //             { channel: 'result', data: '<', action: '' }
// //         );
// //     });

// //     it('should return greater than when left comparison is not equal', () => {
// //         const helper = new MachineHelper(lexCompare());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'cmp', data: null, action: '' },
// //             { channel: 'inner/left/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/result', data: '>', action: '' },
// //             { channel: 'result', data: '>', action: '' }
// //         );
// //     });

// //     it('should continue to right comparison when left is equal', () => {
// //         const helper = new MachineHelper(lexCompare());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'cmp', data: null, action: '' },
// //             { channel: 'inner/left/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/result', data: '=', action: '' },
// //             { channel: 'inner/right/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/right/result', data: '<', action: '' },
// //             { channel: 'result', data: '<', action: '' }
// //         );
// //     });

// //     it('should return right comparison result when left is equal', () => {
// //         const helper = new MachineHelper(lexCompare());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'cmp', data: null, action: '' },
// //             { channel: 'inner/left/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/result', data: '=', action: '' },
// //             { channel: 'inner/right/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/right/result', data: '>', action: '' },
// //             { channel: 'result', data: '>', action: '' }
// //         );
// //     });

// //     it('should return equal when both comparisons are equal', () => {
// //         const helper = new MachineHelper(lexCompare());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'cmp', data: null, action: '' },
// //             { channel: 'inner/left/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/result', data: '=', action: '' },
// //             { channel: 'inner/right/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/right/result', data: '=', action: '' },
// //             { channel: 'result', data: '=', action: '' }
// //         );
// //     });

// //     it('should handle multiple comparisons', () => {
// //         const helper = new MachineHelper(lexCompare());
// //         expect(helper).toAdvanceTo(
// //             { channel: 'cmp', data: null, action: '' },
// //             { channel: 'inner/left/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/result', data: '<', action: '' },
// //             { channel: 'result', data: '<', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'cmp', data: null, action: '' },
// //             { channel: 'inner/left/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/result', data: '=', action: '' },
// //             { channel: 'inner/right/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/right/result', data: '>', action: '' },
// //             { channel: 'result', data: '>', action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'cmp', data: null, action: '' },
// //             { channel: 'inner/left/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/left/result', data: '=', action: '' },
// //             { channel: 'inner/right/cmp', data: null, action: '' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: 'inner/right/result', data: '=', action: '' },
// //             { channel: 'result', data: '=', action: '' }
// //         );
// //     });
// // });

// // function greeter(): Machine {
// //     return {
// //         start(): any {
// //             return { kind: 'start' };
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             if (i.channel !== '') {
// //                 throw new Error('Invalid channel: ' + i.channel);
// //             }
// //             if (s.kind === 'start') {
// //                 if (i.action !== 'getGreeting') {
// //                     throw new Error('Invalid action: ' + i.action);
// //                 }
// //                 return [{ kind: 'awaitName' }, { channel: '', data: null, action: 'getName' }];
// //             }
// //             if (s.kind === 'awaitName') {
// //                 if (i.action !== 'setName') {
// //                     throw new Error('Invalid action: ' + i.action);
// //                 }
// //                 const name = i.data;
// //                 return [{ kind: 'start' }, { channel: '', data: "Hello, " + name + "!", action: 'greet' }];
// //             }
// //             throw new Error('Invalid state: ' + s);
// //         },
// //     }
// // }

// // describe('greeter', () => {
// //     it('should greet the user', () => {
// //         const helper = new MachineHelper(greeter());
// //         expect(helper).toAdvanceTo(
// //             { channel: '', data: null, action: 'getGreeting' },
// //             { channel: '', data: null, action: 'getName' }
// //         );
// //         expect(helper).toAdvanceTo(
// //             { channel: '', data: 'Alice', action: 'setName' },
// //             { channel: '', data: "Hello, Alice!", action: 'greet' }
// //         );
// //     });
// // });

// // function wantsGreeting(name: string): Machine {
// //     return {
// //         start(): any {
// //             return { kind: 'start' };
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             if (s.kind === 'start') {
// //                 if (i.channel !== 'main') {
// //                     throw new Error('Invalid channel: ' + i.channel);
// //                 }
// //                 if (i.action !== 'go') {
// //                     throw new Error('Invalid action: ' + i.action);
// //                 }
// //                 return [{ kind: 'awaitingGreeting' }, { channel: 'greeter', data: null, action: 'getGreeting' }];
// //             }
// //             if (s.kind === 'awaitingGreeting') {
// //                 if (i.channel !== 'greeter') {
// //                     throw new Error('Invalid channel: ' + i.channel);
// //                 }
// //                 if (i.action === 'getName') {
// //                     return [{ kind: 'awaitingGreeting' }, { channel: 'greeter', data: name, action: 'setName' }];
// //                 }
// //                 if (i.action === 'greet') {
// //                     return [{ kind: 'start' }, { channel: 'main', data: "Got greeting: " + i.data, action: 'result' }];
// //                 }
// //                 throw new Error('Invalid action: ' + i.action);
// //             }
// //             throw new Error('Invalid state: ' + s);
// //         },
// //     }
// // }

// // // describe('wantsGreeting', () => {
// // //     it('should ask for a greeting', () => {
// // //         const helper = new MachineHelper(wantsGreeting('Alice'));
// // //         expect(helper).toAdvanceTo(
// // //             { channel: 'main', data: null, action: 'go' },
// // //             { channel: 'greeter', data: null, action: 'getGreeting' }
// // //         );
// // //         expect(helper).toAdvanceTo(
// // //             { channel: 'greeter', data: null, action: 'getName' },
// // //             { channel: 'greeter', data: 'Alice', action: 'setName' }
// // //         );
// // //         expect(helper).toAdvanceTo(
// // //             { channel: 'greeter', data: "yo what up", action: 'greet' },
// // //             { channel: 'main', data: "Got greeting: yo what up", action: 'result' }
// // //         );
// // //     });

// // //     it('double wants greeting', () => {
// // //         const pair = product(wantsGreeting('Alice'), wantsGreeting('Bob'));
// // //         const helper = new MachineHelper(pair);
// // //         expect(helper).toAdvanceTo(
// // //             { channel: 'left/result', data: null, action: '' },
// // //             { channel: 'left/greeter/hello', data: { name: 'Alice' }, action: '' }
// // //         );
// // //         expect(helper).toAdvanceTo(
// // //             { channel: 'right/result', data: null, action: '' },
// // //             { channel: 'right/greeter/hello', data: { name: 'Bob' }, action: '' }
// // //         );
// // //     });
// // // });

// // function nameCompare(): Machine {
// //     return {
// //         start(): any {
// //             return { kind: 'start' };
// //         },
// //         advance(s: any, i: Input): [any, Output] {
// //             return [s, { channel: 'result', data: null, action: '' }];
// //         },
// //     }
// // }

// function getThingy(onChannel: string): Machine<any, any, any> {
//     return {
//         start(): any {
//             return { kind: 'start' };
//         },
//         readyForInput(s: any): string[] {
//             if (s.kind === 'start') {
//                 return [];
//             }
//             if (s.kind === 'awaiting') {
//                 return [onChannel];
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//         sendInput(s: any, channel: string, data: any): any {
//             if (s.kind === 'awaiting') {
//                 if (channel !== onChannel) {
//                     throw new Error('Invalid channel: ' + channel);
//                 }
//                 return { kind: 'finished', data };
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//         hasOutput(s: any): string[] {
//             if (s.kind === 'start') {
//                 return [onChannel];
//             }
//             if (s.kind === 'finished') {
//                 return ["result"];
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//         getOutput(s: any, channel: string): [any, any] {
//             if (s.kind === 'start') {
//                 if (channel !== onChannel) {
//                     throw new Error('Invalid channel: ' + channel);
//                 }
//                 return [{ kind: 'awaiting' }, {kind: 'get'}];
//             }
//             if (s.kind === 'finished') {
//                 if (channel !== "result") {
//                     throw new Error('Invalid channel: ' + channel);
//                 }
//                 return [{kind: 'done'}, s.data];
//             }
//             throw new Error('Invalid state: ' + s);
//         },
//         advance(s: any): [any, boolean] {
//             return [s, false];
//         },
//     }
// }

// function composeChannels(m1: Machine<any, any, any>, m2: Machine<any, any, any>, channels: string[], otherChannels: string[]): Machine<any, any, any> {
//     const pair = product({ left: m1, right: m2 });
//     return pair;
// }

// describe('getThingy', () => {
//     it('should output on the specified channel initially', () => {
//         const helper = new MachineHelper(getThingy('foo'));
//         const state = helper['state'];
//         const hasOutput = helper['machine'].hasOutput(state);
//         expect(hasOutput).toEqual(['foo']);
//     });

//     it('should transition to awaiting state when getting output', () => {
//         const helper = new MachineHelper(getThingy('foo'));
//         const state = helper['state'];
//         const [newState, output] = helper['machine'].getOutput(state, 'foo');
//         expect(newState).toEqual({ kind: 'awaiting' });
//         expect(output).toEqual({ kind: 'get' });
//     });

//     it('should be ready for input on the channel after getting output', () => {
//         const helper = new MachineHelper(getThingy('bar'));
//         const state = helper['state'];
//         const [newState] = helper['machine'].getOutput(state, 'bar');
//         const readyChannels = helper['machine'].readyForInput(newState);
//         expect(readyChannels).toEqual(['bar']);
//     });

//     it('should accept input and transition to finished state', () => {
//         const helper = new MachineHelper(getThingy('baz'));
//         let state = helper['state'];
//         [state] = helper['machine'].getOutput(state, 'baz');
//         state = helper['machine'].sendInput(state, 'baz', 42);
//         expect(state).toEqual({ kind: 'finished', data: 42 });
//     });

//     it('should output the received data on result channel', () => {
//         const helper = new MachineHelper(getThingy('test'));
//         let state = helper['state'];
//         [state] = helper['machine'].getOutput(state, 'test');
//         state = helper['machine'].sendInput(state, 'test', 'hello');
//         const hasOutput = helper['machine'].hasOutput(state);
//         expect(hasOutput).toEqual(['result']);
//         const [finalState, output] = helper['machine'].getOutput(state, 'result');
//         expect(output).toEqual('hello');
//         expect(finalState).toEqual({ kind: 'done' });
//     });

//     it('should work with MachineHelper advance method', () => {
//         const helper = new MachineHelper(getThingy('data'));
//         // First advance: get output on 'data' channel
//         const result1 = helper.advance('', null);
//         expect(result1.channel).toBe('data');
//         expect(result1.data).toEqual({ kind: 'get' });
        
//         // Second advance: send input on 'data' channel and get result
//         const result2 = helper.advance('data', 'test value');
//         expect(result2.channel).toBe('result');
//         expect(result2.data).toBe('test value');
//     });

//     it('should handle numeric data', () => {
//         const helper = new MachineHelper(getThingy('number'));
//         helper.advance('', null); // Get initial output
//         const result = helper.advance('number', 123);
//         expect(result.channel).toBe('result');
//         expect(result.data).toBe(123);
//     });

//     it('should handle object data', () => {
//         const helper = new MachineHelper(getThingy('obj'));
//         helper.advance('', null); // Get initial output
//         const testObj = { a: 1, b: 'test' };
//         const result = helper.advance('obj', testObj);
//         expect(result.channel).toBe('result');
//         expect(result.data).toEqual(testObj);
//     });

//     it('should handle different channel names', () => {
//         const helper1 = new MachineHelper(getThingy('channel1'));
//         const helper2 = new MachineHelper(getThingy('channel2'));
        
//         const result1 = helper1.advance('', null);
//         expect(result1.channel).toBe('channel1');
        
//         const result2 = helper2.advance('', null);
//         expect(result2.channel).toBe('channel2');
//     });

//     it('should throw error when getting output from wrong channel initially', () => {
//         const helper = new MachineHelper(getThingy('correct'));
//         const state = helper['state'];
//         expect(() => {
//             helper['machine'].getOutput(state, 'wrong');
//         }).toThrow('Invalid channel: wrong');
//     });

//     it('should throw error when sending input on wrong channel', () => {
//         const helper = new MachineHelper(getThingy('correct'));
//         let state = helper['state'];
//         [state] = helper['machine'].getOutput(state, 'correct');
//         expect(() => {
//             helper['machine'].sendInput(state, 'wrong', 'data');
//         }).toThrow('Invalid channel: wrong');
//     });

//     it('should throw error when getting result from wrong channel', () => {
//         const helper = new MachineHelper(getThingy('test'));
//         let state = helper['state'];
//         [state] = helper['machine'].getOutput(state, 'test');
//         state = helper['machine'].sendInput(state, 'test', 'data');
//         expect(() => {
//             helper['machine'].getOutput(state, 'wrong');
//         }).toThrow('Invalid channel: wrong');
//     });

//     it('should do a parallel fetch with product', () => {
//         const helper = new MachineHelper(product({ left: getThingy('foo'), right: getThingy('bar') }));
//         expect(helper.hasOutput()).toEqual(['left/foo', 'right/bar']);
//         expect(helper.getOutput('left/foo')).toEqual({ kind: 'get' });
//         expect(helper.readyForInput()).toEqual(['left/foo']);
//         helper.sendInput('left/foo', 'data');
//         expect(helper.hasOutput()).toEqual(['left/result', 'right/bar']);

//     });
// });