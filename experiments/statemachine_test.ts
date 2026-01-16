type Input = {
    channel: string;
    data: any;
}

type Output = {
    channel: string;
    data: any;
}

type Machine = {
    start(): any;
    advance(s: any, i: Input): [any, Output];
}

// Test helper: runs a machine through a list of inputs and asserts the outputs match
function runMachine(machine: Machine, ioPairs: Array<{ input: Input, output: Output }>): void {
    let state = machine.start();
    for (let i = 0; i < ioPairs.length; i++) {
        const { input, output: expectedOutput } = ioPairs[i];
        const [newState, actualOutput] = machine.advance(state, input);
        try {
            expect(actualOutput).toEqual(expectedOutput);
        } catch (error) {
            // Re-throw with context about which test case failed, preserving Jest's error details
            const context = `\n\n=== Test case ${i} failed (0-indexed) ===\n  Input: ${JSON.stringify(input, null, 2)}\n  Expected: ${JSON.stringify(expectedOutput, null, 2)}\n  Received: ${JSON.stringify(actualOutput, null, 2)}\n`;
            if (error instanceof Error) {
                error.message = context + error.message;
                throw error;
            }
            throw new Error(context + String(error));
        }
        state = newState;
    }
}

function constant(data: any): Machine {
    return {
        start(): any {
            return null;
        },
        advance(s: any, i: Input): [any, Output] {
            if (i.channel !== "result") {
                throw new Error('Invalid channel: ' + i.channel);
            }
            return [s, { channel: "break/result", data: data }];
        },
    }
}

describe('constant', () => {
    it('should throw an error if the channel is invalid', () => {
        const machine = constant('data');
        expect(() => machine.advance(null, { channel: 'invalid', data: 'data' })).toThrow('Invalid channel: invalid');
    });
    it('should return the data', () => {
        const machine = constant('data');
        const [state, output] = machine.advance(null, { channel: 'result', data: 'data' });
        expect(output).toEqual({ channel: 'break/result', data: 'data' });
    });
    it('should handle multiple inputs correctly', () => {
        const machine = constant('data');
        runMachine(machine, [
            { input: { channel: 'result', data: 'input1' }, output: { channel: 'break/result', data: 'data' } },
            { input: { channel: 'result', data: 'input2' }, output: { channel: 'break/result', data: 'data' } },
            { input: { channel: 'result', data: 'input3' }, output: { channel: 'break/result', data: 'data' } },
        ]);
    });
});

function compose(m1: Machine, m1_channel: string, m2: Machine, m2_channel: string): Machine {
    return {
        start(): [any, any] {
            return [m1.start(), m2.start()];
        },
        advance([s1, s2]: [any, any], i: Input): [any, Output] {
            const [new_s1, o1] = m1.advance(s1, i);
            if (o1.channel === m1_channel) {
                const [new_s2, o2] = m2.advance(s2, { channel: m2_channel, data: o1.data });
                return [[new_s1, new_s2], { channel: '2/' + o2.channel, data: o2.data }];
            } else {
                return [[new_s1, s2], { channel: '1/' + m1_channel, data: o1.data }];
            }
        },
    }
}

// describe('compose', () => {
//     it('should return start states from both machines', () => {
//         const m1 = constant('data1');
//         const m2 = constant('data2');
//         const composed = compose(m1, 'result', m2, 'result');
//         const start = composed.start();
//         expect(start).toEqual([null, null]);
//     });

//     it('should forward to m2 when m1 output matches m1_channel', () => {
//         const m1 = constant('data1');
//         const m2 = constant('data2');
//         const composed = compose(m1, 'result', m2, 'result');
//         const [state, output] = composed.advance([null, null], {channel: 'result', data: 'input'});
//         expect(output).toEqual({channel: '2/result', data: 'data2'});
//         expect(state).toEqual([null, null]);
//     });

//     it('should return m1 output when it does not match m1_channel', () => {
//         const m1 = constant('data1');
//         const m2 = constant('data2');
//         const composed = compose(m1, 'forward', m2, 'forward');
//         const [state, output] = composed.advance([null, null], {channel: 'result', data: 'input'});
//         expect(output).toEqual({channel: '1/forward', data: 'data1'});
//         expect(state).toEqual([null, null]);
//     });

//     it('should pass m1 output data to m2 when forwarding', () => {
//         const m1 = constant('data_from_m1');
//         const m2 = constant('data2');
//         const composed = compose(m1, 'result', m2, 'result');
//         const [state, output] = composed.advance([null, null], {channel: 'result', data: 'input'});
//         // m2 should receive 'data_from_m1' as input data
//         expect(output).toEqual({channel: '2/result', data: 'data2'});
//     });

// });

// Runs a until it is terminal, then runs the matching b from b_map.
function sequence(a: Machine, b: Machine): Machine {
    return {
        start(): [string, any] {
            return ['a', a.start()];
        },
        advance([state, s]: [string, any], i: Input): [any, Output] {
            if (state === 'a') {
                const [new_s, o] = a.advance(s, i);
                if (o.channel.startsWith('continue/')) {
                    return [['a', new_s], { channel: o.channel, data: o.data }];
                }
                if (o.channel.startsWith('break/')) {
                    return [['b', b.start()], { channel: 'continue/' + o.channel.substring('break/'.length), data: o.data }];
                }
                throw new Error('Invalid channel: ' + o.channel);
            }
            if (state === 'b') {
                const [new_s, o] = b.advance(s, i);
                if (o.channel.startsWith('continue/')) {
                    return [['b', new_s], { channel: o.channel, data: o.data }];
                }
                if (o.channel.startsWith('break/')) {
                    return [['end', null], { channel: o.channel, data: o.data }];
                }
                throw new Error('Invalid channel: ' + o.channel);
            }
            throw new Error('Invalid state: ' + state);
        },
    }
}

describe('sequence', () => {
    it('should start in A phase and then B phase', () => {
        const a = constant('data1');
        const b = constant('data2');
        const seq = sequence(a, b);
        runMachine(seq, [
            { input: { channel: 'result', data: 'ignored1' }, output: { channel: 'continue/result', data: 'data1' } },
            { input: { channel: 'result', data: 'ignored2' }, output: { channel: 'break/result', data: 'data2' } },
        ]);
    });
});

function func(f: (input: any) => any): Machine {
    return {
        start(): any {
            return 'start';
        },
        advance(s: any, i: Input): [any, Output] {
            if (i.channel !== 'result') {
                throw new Error('Invalid channel: ' + i.channel);
            }
            return ['end', { channel: 'break/result', data: f(i.data) }];
        },
    }
}
function yld(channel: string): Machine {
    return {
        start(): any {
            return 'start';
        },
        advance(s: any, i: Input): [any, Output] {
            if (s === 'start') {
                if (i.channel !== "result") {
                    throw new Error('Invalid channel: ' + i.channel);
                }
                return ['awaiting', { channel: 'continue/' + channel, data: i.data }];
            }
            if (s === 'awaiting') {
                if (i.channel !== channel) {
                    throw new Error('Invalid channel: ' + i.channel);
                }
                return ['end', { channel: "break/result", data: i.data }];
            }
            throw new Error('Invalid state: ' + s);
        },
    }
}

function brk(): Machine {
    return {
        start(): any {
            return 'start';
        },
        advance(s: any, i: Input): [any, Output] {
            if (i.channel !== 'result') {
                throw new Error('Invalid channel: ' + i.channel);
            }
            return ['end', { channel: 'break/result', data: i.data }];
        },
    }
}

function stash(inner: Machine): Machine {
    return {
        start(): any {
            return { kind: 'start' };
        },
        advance(s: any, i: Input): [any, Output] {
            if (s.kind === 'start') {
                if (i.channel !== 'result') {
                    throw new Error('Invalid channel: ' + i.channel);
                }
                let [new_inner, output] = inner.advance(inner.start(), { channel: 'result', data: i.data[1] });

                if (output.channel.startsWith('break/')) {
                    return [{ kind: 'end' }, { channel: output.channel, data: [i.data[0], output.data] }];
                }
                return [{ kind: 'running', stashed: i.data[0], inner: new_inner }, output];
            }
            if (s.kind === 'running') {
                let [new_inner, output] = inner.advance(s.inner, i);
                if (output.channel.startsWith('break/')) {
                    return [{ kind: 'end' }, { channel: output.channel, data: [s.stashed, output.data] }];
                }
                return [{ kind: 'running', stashed: s.stashed, inner: new_inner }, output];
            }
            throw new Error('Invalid state: ' + s);
        },
    }
}

function pipeline(machine: Machine): Machine {
    return {
        start(): any {
            return machine.start();
        },
        advance(s: any, i: Input): [any, Output] {
            while (true) {
                const [new_s, output] = machine.advance(s, i);
                if (output.channel !== 'continue/result') {
                    return [new_s, output];
                }
                s = new_s;
                i = { channel: 'result', data: output.data };
            }
            return [s, i]
        },
    }
}

describe('yld', () => {
    it('func with yld', () => {
        const f = func((x: any) => [x + 1, 'hello world']);
        const y = yld('channel');
        const g = func(([x, y]: [number, string]) => '' + y + "/" + x);
        const machine = sequence(f, sequence(stash(y), sequence(g, brk())));
        runMachine(machine, [
            { input: { channel: 'result', data: 4 }, output: { channel: 'continue/result', data: [5, 'hello world'] } },
            { input: { channel: 'result', data: [5, 'hello world'] }, output: { channel: 'continue/channel', data: 'hello world' } },
            { input: { channel: 'channel', data: 'my guy' }, output: { channel: 'continue/result', data: [5, 'my guy'] } },
            { input: { channel: 'result', data: [5, 'my guy'] }, output: { channel: 'continue/result', data: 'my guy/5' } },
            { input: { channel: 'result', data: 'my guy/5' }, output: { channel: 'break/result', data: 'my guy/5' } },
        ]);
    });

    it('func with yld pipelined', () => {
        const f = func((x: any) => [x + 1, 'hello world']);
        const y = yld('channel');
        const g = func(([x, y]: [number, string]) => '' + y + "/" + x);
        const machine = pipeline(sequence(f, sequence(stash(y), sequence(g, brk()))));
        runMachine(machine, [
            { input: { channel: 'result', data: 4 }, output: { channel: 'continue/channel', data: 'hello world' } },
            { input: { channel: 'channel', data: 'my guy' }, output: { channel: 'break/result', data: 'my guy/5' } },
        ]);
    });
});