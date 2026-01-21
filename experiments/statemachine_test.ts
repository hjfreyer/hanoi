
class MachineHelper {
    private state: any;
    constructor(private machine: Machine) {
        this.state = machine.start();
    }

    advance(i: Input): Output {
        const [newState, output] = this.machine.advance(this.state, i);
        this.state = newState;
        return output;
    }
}

// Custom Jest matcher for MachineHelper
expect.extend({
    toAdvanceTo(received: MachineHelper, input: Input, expectedOutput: Output) {
        const actualOutput = received.advance(input);
        const pass = this.equals(actualOutput, expectedOutput);
        
        if (pass) {
            return {
                message: () => `Expected machine not to advance to ${this.utils.printExpected(expectedOutput)}`,
                pass: true,
            };
        } else {
            return {
                message: () => 
                    `Expected machine to advance to:\n` +
                    `  ${this.utils.printExpected(expectedOutput)}\n` +
                    `Received:\n` +
                    `  ${this.utils.printReceived(actualOutput)}\n` +
                    `Input was:\n` +
                    `  ${this.utils.printReceived(input)}`,
                pass: false,
            };
        }
    },
});

// TypeScript declarations for the custom matcher
declare global {
    namespace jest {
        interface Matchers<R> {
            toAdvanceTo(input: Input, expectedOutput: Output): R;
        }
    }
}

export {};

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
            const context = `\n\n=== Test case ${i} failed (0-indexed) ===\n  State: ${JSON.stringify(state, null, 2)}\n  Input: ${JSON.stringify(input, null, 2)}\n  Expected: ${JSON.stringify(expectedOutput, null, 2)}\n  Received: ${JSON.stringify(actualOutput, null, 2)}\n  New State: ${JSON.stringify(newState, null, 2)}\n`;
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
        const helper = new MachineHelper(constant('data'));
        expect(helper).toAdvanceTo(
            { channel: 'result', data: 'input1' },
            { channel: 'break/result', data: 'data' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'result', data: 'input2' },
            { channel: 'break/result', data: 'data' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'result', data: 'input3' },
            { channel: 'break/result', data: 'data' }
        );
    });
});

function composeSingle(m1: Machine, m2: Machine): Machine {
    return {
        start(): [any, any] {
            return [m1.start(), m2.start()];
        },
        advance([s1, s2]: [any, any], i: Input): [any, Output] {
            const [new_s1, o1] = m1.advance(s1, i);
            const [new_s2, o2] = m2.advance(s2, { channel: o1.channel, data: o1.data });
            return [[new_s1, new_s2], { channel: o2.channel, data: o2.data }];
        },
    }
}

function compose(...machines: Machine[]): Machine {
    if (machines.length === 0) {
        throw new Error('compose requires at least one machine');
    }
    if (machines.length === 1) {
        return machines[0];
    }
    let result = machines[0];
    for (let i = 1; i < machines.length; i++) {
        result = composeSingle(result, machines[i]);
    }
    return result;
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
function sequenceSingle(a: Machine, b: Machine): Machine {
    return {
        start(): [string, any] {
            return ['a', a.start()];
        },
        advance([state, s]: [string, any], i: Input): [any, Output] {
            if (state === 'a') {
                const [new_s, o] = a.advance(s, i);
                if (o.channel.startsWith('continue/') || o.channel.startsWith('yield/')) {
                    return [['a', new_s], { channel: o.channel, data: o.data }];
                }
                if (o.channel.startsWith('break/')) {
                    return [['b', b.start()], { channel: 'continue/' + o.channel.substring('break/'.length), data: o.data }];
                }
                throw new Error('Invalid channel: ' + o.channel);
            }
            if (state === 'b') {
                const [new_s, o] = b.advance(s, i);
                if (o.channel.startsWith('continue/') || o.channel.startsWith('yield/')) {
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

function sequence(...machines: Machine[]): Machine {
    if (machines.length === 0) {
        throw new Error('sequence requires at least one machine');
    }
    if (machines.length === 1) {
        return machines[0];
    }
    let result = machines[0];
    for (let i = 1; i < machines.length; i++) {
        result = sequenceSingle(result, machines[i]);
    }
    return result;
}

describe('sequence', () => {
    it('should start in A phase and then B phase', () => {
        const helper = new MachineHelper(sequenceSingle(constant('data1'), constant('data2')));
        expect(helper).toAdvanceTo(
            { channel: 'result', data: 'ignored1' },
            { channel: 'continue/result', data: 'data1' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'result', data: 'ignored2' },
            { channel: 'break/result', data: 'data2' }
        );
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
                return ['awaiting', { channel: 'yield/' + channel, data: i.data }];
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
        const helper = new MachineHelper(sequence(f, stash(y), g, brk()));
        expect(helper).toAdvanceTo(
            { channel: 'result', data: 4 },
            { channel: 'continue/result', data: [5, 'hello world'] }
        );
        expect(helper).toAdvanceTo(
            { channel: 'result', data: [5, 'hello world'] },
            { channel: 'yield/channel', data: 'hello world' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'channel', data: 'my guy' },
            { channel: 'continue/result', data: [5, 'my guy'] }
        );
        expect(helper).toAdvanceTo(
            { channel: 'result', data: [5, 'my guy'] },
            { channel: 'continue/result', data: 'my guy/5' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'result', data: 'my guy/5' },
            { channel: 'break/result', data: 'my guy/5' }
        );
    });

    it('func with yld pipelined', () => {
        const f = func((x: any) => [x + 1, 'hello world']);
        const y = yld('channel');
        const g = func(([x, y]: [number, string]) => '' + y + "/" + x);
        const helper = new MachineHelper(loop(sequence(f, stash(y), g, brk())));
        expect(helper).toAdvanceTo(
            { channel: 'result', data: 4 },
            { channel: 'channel', data: 'hello world' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'channel', data: 'my guy' },
            { channel: 'result', data: 'my guy/5' }
        );
    });
});

function array(size: number): Machine {
    return {
        start(): any {
            return { kind: 'ready', arr: Array(size).fill(null) };
        },
        advance(s: any, i: Input): [any, Output] {
            if (s.kind === 'ready') {
                const arr = s.arr;
                if (i.channel === "set") {
                    const [idx, value] = i.data;
                    if (idx < 0 || idx >= size) {
                        return [arr, { channel: 'err', data: 'invalid index: ' + idx }];
                    }
                    arr[idx] = value;
                    return [{ kind: 'ready', arr: arr }, { channel: 'result', data: null }];
                }
                if (i.channel === "take") {
                    const idx = i.data;
                    if (idx < 0 || idx >= size) {
                        return [{ kind: 'ready', arr: arr }, { channel: 'err', data: 'invalid index: ' + idx }];
                    }
                    return [{ kind: 'incomplete', arr: arr, idx: idx }, { channel: 'result', data: arr[idx] }];
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            if (s.kind === 'incomplete') {
                const arr = s.arr;
                const idx = s.idx;
                if (i.channel === "set") {
                    const [idx2, value] = i.data;
                    if (idx2 !== idx) {
                        return [s, { channel: 'err', data: 'invalid index: ' + idx2 }];
                    }
                    arr[idx] = value;
                    return [{ kind: 'ready', arr: arr }, { channel: 'result', data: null }];
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            throw new Error('Invalid state: ' + s);
        },
    }
}

describe('array', () => {
    it('should set values at valid indices', () => {
        const helper = new MachineHelper(array(3));
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [0, 'first'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [1, 'second'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [2, 'third'] },
            { channel: 'result', data: null }
        );
    });

    it('should take values at valid indices', () => {
        const helper = new MachineHelper(array(3));
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [0, 'value0'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [1, 'value1'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'take', data: 0 },
            { channel: 'result', data: 'value0' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [0, 'value0'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'take', data: 1 },
            { channel: 'result', data: 'value1' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [1, 'value1'] },
            { channel: 'result', data: null }
        );
    });

    it('should return null for uninitialized indices', () => {
        const helper = new MachineHelper(array(3));
        expect(helper).toAdvanceTo(
            { channel: 'take', data: 0 },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [0, null] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'take', data: 1 },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [1, null] },
            { channel: 'result', data: null }
        );
    });

    it('should handle take-then-set pattern in incomplete state', () => {
        const helper = new MachineHelper(array(3));
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [0, 'initial'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'take', data: 0 },
            { channel: 'result', data: 'initial' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [0, 'updated'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'take', data: 0 },
            { channel: 'result', data: 'updated' }
        );
    });

    it('should error on invalid index for set', () => {
        const arr = array(3);
        expect(() => {
            const [state, output] = arr.advance(arr.start(), { channel: 'set', data: [5, 'value'] });
            if (output.channel === 'err') {
                throw new Error(output.data);
            }
        }).toThrow('invalid index: 5');
    });

    it('should error on negative index for set', () => {
        const arr = array(3);
        expect(() => {
            const [state, output] = arr.advance(arr.start(), { channel: 'set', data: [-1, 'value'] });
            if (output.channel === 'err') {
                throw new Error(output.data);
            }
        }).toThrow('invalid index: -1');
    });

    it('should error on invalid index for take', () => {
        const arr = array(3);
        expect(() => {
            const [state, output] = arr.advance(arr.start(), { channel: 'take', data: 10 });
            if (output.channel === 'err') {
                throw new Error(output.data);
            }
        }).toThrow('invalid index: 10');
    });

    it('should error on wrong index in incomplete state', () => {
        const arr = array(3);
        let state = arr.start();
        const [state1, output1] = arr.advance(state, { channel: 'take', data: 0 });
        expect(() => {
            const [state2, output2] = arr.advance(state1, { channel: 'set', data: [1, 'wrong'] });
            if (output2.channel === 'err') {
                throw new Error(output2.data);
            }
        }).toThrow('invalid index: 1');
    });

    it('should handle multiple operations correctly', () => {
        const helper = new MachineHelper(array(5));
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [0, 'a'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [1, 'b'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [2, 'c'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'take', data: 0 },
            { channel: 'result', data: 'a' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [0, 'A'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'take', data: 1 },
            { channel: 'result', data: 'b' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [1, 'B'] },
            { channel: 'result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'take', data: 2 },
            { channel: 'result', data: 'c' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'set', data: [2, 'C'] },
            { channel: 'result', data: null }
        );
    });
});

function advancePrimitive(s: any, i: Input): [any, Output] {
    const channel = i.channel.split('/');
    if (channel[0] === 'set') {
        return [i.data, { channel: 'set', data: null }];
    }
    if (channel[0] === 'copy') {
        return [s, { channel: 'copy', data: s }];
    }
    if (channel[0] === 'element') {
        if (!Array.isArray(s)) {
            return [s, { channel: 'err', data: 'not an array' }];
        }
        const idx = parseInt(channel[1]);
        if (idx < 0 || idx >= s.length) {
            return [s, { channel: 'err', data: 'invalid index: ' + idx }];
        }
        const subchannel = channel.slice(2).join('/');
        const [new_s, output] = advancePrimitive(s[idx], { channel: subchannel, data: i.data });
        s[idx] = new_s;
        return [s, { channel: 'element/' + idx + '/' + output.channel, data: output.data }];
    }
    throw new Error('Invalid channel: ' + i.channel);
}

function primitive(): Machine {
    return {
        start(): any {
            return null;
        },
        advance(s: any, i: Input): [any, Output] {
            return advancePrimitive(s, i);
        },
    }
}

function name2(): Machine {
    return {
        start(): any {
            return { kind: 'start' };
        },
        advance(s: any, i: Input): [any, Output] {
            const channel = i.channel.split('/');
            if (s.kind === 'start') {
                if (channel[0] === 'first') {
                    const subchannel = channel.slice(1).join('/');
                    return [{ kind: 'awaitingFirst' }, { channel: 'inner/left/' + subchannel, data: i.data }];
                }
                if (channel[0] === 'last') {
                    const subchannel = channel.slice(1).join('/');
                    return [{ kind: 'awaitingLast' }, { channel: 'inner/right/' + subchannel, data: i.data }];
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            if (s.kind === 'awaitingFirst') {
                if (i.channel === 'inner/left/result') {
                    return [{ kind: 'start' }, { channel: 'first/result', data: i.data }];
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            if (s.kind === 'awaitingLast') {
                if (i.channel === 'inner/right/result') {
                    return [{ kind: 'start' }, { channel: 'last/result', data: i.data }];
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            throw new Error('Invalid state: ' + s);
        },
    }
}

function name(): Machine {
    return renameChannels({
        'inner/left': 'first',
        'inner/right': 'last',
        'first': 'inner/left',
        'last': 'inner/right',
    });
}

function product(m1: Machine, m2: Machine): Machine {
    return {
        start(): any {
            return [m1.start(), m2.start()];
        },
        advance([s1, s2]: [any, any], i: Input): [any, Output] {
            const channel = i.channel.split('/');
            if (channel[0] === 'left') {
                const [new_s1, o1] = m1.advance(s1, { channel: channel.slice(1).join('/'), data: i.data });
                return [[new_s1, s2], { channel: 'left/' + o1.channel, data: o1.data }];
            }
            if (channel[0] === 'right') {
                const [new_s2, o2] = m2.advance(s2, { channel: channel.slice(1).join('/'), data: i.data });
                return [[s1, new_s2], { channel: 'right/' + o2.channel, data: o2.data }];
            }
            throw new Error('Invalid channel: ' + i.channel);
        },
    }
}

function nameBindPrimitive(inner: Machine): Machine {
    return {
        start(): any {
            return { primitive: inner.start(), name: name().start() };
        },
        advance(s: any, i: Input): [any, Output] {
            let [name_s, name_output] = name().advance(s.name, i);
            let channel = name_output.channel.split('/');
            let primitive_s = s.primitive;
            while (channel[0] === 'inner') {
                const subchannel = channel.slice(1).join('/');
                const [new_primitive_s, primitive_output] = inner.advance(primitive_s, { channel: subchannel, data: name_output.data });
                primitive_s = new_primitive_s;
                [name_s, name_output] = name().advance(name_s, { channel: 'inner/' + primitive_output.channel, data: primitive_output.data });
                channel = name_output.channel.split('/');
            }
            if (channel[0] === 'result' || channel[0] === 'first' || channel[0] === 'second') {
                return [{ primitive: primitive_s, name: name_s }, { channel: name_output.channel, data: name_output.data }];
            }
            throw new Error('Invalid channel: ' + name_output.channel);
        },
    }
}

function renameChannel(old_channel: string, new_channel: string): Machine {
    return {
        start(): any {
            return null;
        },
        advance(s: null, i: Input): [any, Output] {
            const channel = i.channel.split('/');
            const old_channel_parts = old_channel.split('/');
            const new_channel_parts = new_channel.split('/');
            // Check if the prefix of channel matches old_channel
            if (channel.length >= old_channel_parts.length) {
                let matches = true;
                for (let i = 0; i < old_channel_parts.length; i++) {
                    if (channel[i] !== old_channel_parts[i]) {
                        matches = false;
                        break;
                    }
                }
                if (matches) {
                    return [null, { channel: [...new_channel_parts, ...channel.slice(old_channel_parts.length)].join('/'), data: i.data }];
                }
            }
            return [null, { channel: i.channel, data: i.data }];
        },
    }
}

function renameChannels(renames: Record<string, string>): Machine {
    return {
        start(): any {
            return null;
        },
        advance(s: null, i: Input): [any, Output] {
            const channel = i.channel.split('/');
            // Find the longest matching prefix
            let bestMatch: { oldParts: string[], newParts: string[] } | null = null;
            let bestLength = -1;

            for (const [old_channel, new_channel] of Object.entries(renames)) {
                const old_channel_parts = old_channel.split('/');
                // Handle empty prefix: '' should match everything
                const effectiveLength = (old_channel_parts.length === 1 && old_channel_parts[0] === '') ? 0 : old_channel_parts.length;
                
                if (channel.length >= effectiveLength && effectiveLength > bestLength) {
                    let matches = true;
                    // Empty prefix always matches
                    if (effectiveLength > 0) {
                        for (let j = 0; j < old_channel_parts.length; j++) {
                            if (channel[j] !== old_channel_parts[j]) {
                                matches = false;
                                break;
                            }
                        }
                    }
                    if (matches) {
                        bestMatch = { oldParts: old_channel_parts, newParts: new_channel.split('/') };
                        bestLength = effectiveLength;
                    }
                }
            }

            if (bestMatch) {
                const remainingParts = channel.slice(bestLength);
                // Handle empty new_channel: if newParts is [''] and there are remaining parts, just use remaining parts
                if (bestMatch.newParts.length === 1 && bestMatch.newParts[0] === '' && remainingParts.length > 0) {
                    return [null, { channel: remainingParts.join('/'), data: i.data }];
                }
                return [null, { channel: [...bestMatch.newParts, ...remainingParts].join('/'), data: i.data }];
            }
            return [null, { channel: i.channel, data: i.data }];
        },
    }
}

describe('renameChannels', () => {
    it('should rename channels', () => {
        const helper = new MachineHelper(renameChannels({ 'inner/left': 'first', 'inner/right': 'last' }));
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/set', data: 'a' },
            { channel: 'first/set', data: 'a' }
        );
    });
    it('should support empty prefix', () => {
        const helper = new MachineHelper(renameChannels({ '': 'first' }));
        expect(helper).toAdvanceTo(
            { channel: 'set', data: 'a' },
            { channel: 'first/set', data: 'a' }
        );
    });
    it('should support renaming to empty value', () => {
        const helper = new MachineHelper(renameChannels({ 'first': '' }));
        expect(helper).toAdvanceTo(
            { channel: 'first/set', data: 'a' },
            { channel: 'set', data: 'a' }
        );
    });
});

function loop(inner: Machine): Machine {
    return {
        start(): any {
            return inner.start();
        },
        advance(s: any, i: Input): [any, Output] {
            let [inner_s, inner_output] = inner.advance(s, i);
            let channel = inner_output.channel.split('/');
            while (channel[0] === 'continue') {
                const subchannel = channel.slice(1).join('/');
                [inner_s, inner_output] = inner.advance(inner_s, { channel: subchannel, data: inner_output.data });
                channel = inner_output.channel.split('/');
            }
            if (channel[0] === 'break') {
                const subchannel = channel.slice(1).join('/');
                return [inner_s, { channel: subchannel, data: inner_output.data }];
            }
            if (channel[0] === 'yield') {
                return [inner_s, { channel: channel.slice(1).join('/'), data: inner_output.data }];
            }
            throw new Error('Invalid channel: ' + inner_output.channel);
        },
    }
}

describe('name', () => {
    it('should allow accessing elements of the name unbound', () => {
        const helper = new MachineHelper(name());
        expect(helper).toAdvanceTo(
            { channel: 'first/set', data: 'a' },
            { channel: 'inner/left/set', data: 'a' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/result', data: null },
            { channel: 'first/result', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'first/copy', data: null },
            { channel: 'inner/left/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/result', data: 'a' },
            { channel: 'first/result', data: 'a' }
        );
    });
    it('should allow accessing elements of the name unbound paired', () => {
        const pair = product(primitive(), primitive());
        const name_pair = compose(
            product(name(), pair),
            renameChannel('left/inner', 'continue/right'),
            renameChannel('right', 'continue/left/inner'),
            renameChannel('left/first', 'break/left/first'));
        const helper = new MachineHelper(name_pair);
        expect(helper).toAdvanceTo(
            { channel: 'left/first/set', data: 'a' },
            { channel: 'continue/right/left/set', data: 'a' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'right/left/set', data: 'a' },
            { channel: 'continue/left/inner/left/set', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'left/inner/left/set', data: null },
            { channel: 'break/left/first/set', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'left/first/copy', data: null },
            { channel: 'continue/right/left/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'right/left/copy', data: null },
            { channel: 'continue/left/inner/left/copy', data: 'a' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'left/inner/left/result', data: 'a' },
            { channel: 'break/left/first/result', data: 'a' }
        );
    });
    it('should allow accessing elements of the name', () => {
        const pair = product(primitive(), primitive());
        const name_pair = compose(
            product(name(), pair),
            renameChannel('left/inner', 'continue/right'),
            renameChannel('right', 'continue/left/inner'),
            renameChannel('left/first', 'break/left/first'));
        const n = compose(
            renameChannel('first', 'left/first'),
            renameChannel('second', 'left/second'),
            loop(name_pair),
            renameChannel('left/first', 'first'),
            renameChannel('left/second', 'second'),
        );

        const helper = new MachineHelper(n);
        expect(helper).toAdvanceTo(
            { channel: 'first/set', data: 'a' },
            { channel: 'first/set', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'first/copy', data: null },
            { channel: 'first/copy', data: 'a' }
        );
    });
});

function stringCompare(): Machine {
    return {
        start(): any {
            return { kind: 'start' };
        },
        advance(s: any, i: Input): [any, Output] {
            if (s.kind === 'start') {
                if (i.channel === 'result') {
                    return [{ kind: 'awaitingLeft' }, { channel: 'inner/left/copy', data: null }];
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            if (s.kind === 'awaitingLeft') {
                if (i.channel === 'inner/left/copy') {
                    return [{ kind: 'awaitingRight', left: i.data }, { channel: 'inner/right/copy', data: null }];
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            if (s.kind === 'awaitingRight') {
                if (i.channel === 'inner/right/copy') {
                    function strCmp(left: string, right: string): '<' | '>' | '=' {
                        if (left < right) {
                            return '<';
                        }
                        if (left > right) {
                            return '>';
                        }
                        return '=';
                    }
                    return [{ kind: 'start' }, { channel: 'result', data: strCmp(s.left, i.data) }];
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            throw new Error('Invalid state: ' + s);
        },
    }
}

describe('stringCompare', () => {
    it('should compare strings and return less than', () => {
        const helper = new MachineHelper(stringCompare());
        expect(helper).toAdvanceTo(
            { channel: 'result', data: null },
            { channel: 'inner/left/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/copy', data: 'apple' },
            { channel: 'inner/right/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/right/copy', data: 'banana' },
            { channel: 'result', data: '<' }
        );
    });

    it('should compare strings and return greater than', () => {
        const helper = new MachineHelper(stringCompare());
        expect(helper).toAdvanceTo(
            { channel: 'result', data: null },
            { channel: 'inner/left/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/copy', data: 'zebra' },
            { channel: 'inner/right/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/right/copy', data: 'apple' },
            { channel: 'result', data: '>' }
        );
    });

    it('should compare strings and return equal', () => {
        const helper = new MachineHelper(stringCompare());
        expect(helper).toAdvanceTo(
            { channel: 'result', data: null },
            { channel: 'inner/left/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/copy', data: 'hello' },
            { channel: 'inner/right/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/right/copy', data: 'hello' },
            { channel: 'result', data: '=' }
        );
    });

    it('should handle multiple comparisons', () => {
        const helper = new MachineHelper(stringCompare());
        expect(helper).toAdvanceTo(
            { channel: 'result', data: null },
            { channel: 'inner/left/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/copy', data: 'a' },
            { channel: 'inner/right/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/right/copy', data: 'b' },
            { channel: 'result', data: '<' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'result', data: null },
            { channel: 'inner/left/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/copy', data: 'x' },
            { channel: 'inner/right/copy', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/right/copy', data: 'y' },
            { channel: 'result', data: '<' }
        );
    });

    it('should work with binding', () => {
        const testBody = loop(sequence(
            constant('a'),
            yld('pair/left/set'),
            constant('b'),
            yld('pair/right/set'),
            compose(
                renameChannels({
                    'pair': 'inner',
                }),
                stringCompare(),
                renameChannels({
                    'inner': 'yield/pair',
                    'result': 'break/result',
                }),
            )
        ));

        const dataPair = product(primitive(), primitive());
        const boundBody = compose(
            product(testBody, dataPair),
            renameChannels({
                'left/pair': 'continue/right',
                'right': 'continue/left/pair',
                'left/result': 'break/left/result',
            }),
        );
        const boundLoop = compose(renameChannels({ '': 'left' }), loop(boundBody), renameChannels({ 'left': '' }));
        const helper = new MachineHelper(boundLoop);
        expect(helper).toAdvanceTo(
            { channel: 'result', data: null },
            { channel: 'result', data: '<' }
        );
    });
});


function lexCompare(): Machine {
    return {
        start(): any {
            return { kind: 'start' };
        },
        advance(s: any, i: Input): [any, Output] {
            if (s.kind === 'start') {
                if (i.channel === 'cmp') {
                    return [{ kind: 'awaitingLeft' }, { channel: 'inner/left/cmp', data: null }];
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            if (s.kind === 'awaitingLeft') {
                if (i.channel === 'inner/left/result') {
                    if (i.data === '=') {
                        return [{ kind: 'awaitingRight' }, { channel: 'inner/right/cmp', data: null }];
                    } else {
                        return [{ kind: 'start' }, { channel: 'result', data: i.data }];
                    }
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            if (s.kind === 'awaitingRight') {
                if (i.channel === 'inner/right/result') {
                    return [{ kind: 'start' }, { channel: 'result', data: i.data }];
                }
                throw new Error('Invalid channel: ' + i.channel);
            }
            throw new Error('Invalid state: ' + s);
        },
    }
}

describe('lexCompare', () => {
    it('should return result immediately when left comparison is not equal', () => {
        const helper = new MachineHelper(lexCompare());
        expect(helper).toAdvanceTo(
            { channel: 'cmp', data: null },
            { channel: 'inner/left/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/result', data: '<' },
            { channel: 'result', data: '<' }
        );
    });

    it('should return greater than when left comparison is not equal', () => {
        const helper = new MachineHelper(lexCompare());
        expect(helper).toAdvanceTo(
            { channel: 'cmp', data: null },
            { channel: 'inner/left/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/result', data: '>' },
            { channel: 'result', data: '>' }
        );
    });

    it('should continue to right comparison when left is equal', () => {
        const helper = new MachineHelper(lexCompare());
        expect(helper).toAdvanceTo(
            { channel: 'cmp', data: null },
            { channel: 'inner/left/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/result', data: '=' },
            { channel: 'inner/right/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/right/result', data: '<' },
            { channel: 'result', data: '<' }
        );
    });

    it('should return right comparison result when left is equal', () => {
        const helper = new MachineHelper(lexCompare());
        expect(helper).toAdvanceTo(
            { channel: 'cmp', data: null },
            { channel: 'inner/left/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/result', data: '=' },
            { channel: 'inner/right/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/right/result', data: '>' },
            { channel: 'result', data: '>' }
        );
    });

    it('should return equal when both comparisons are equal', () => {
        const helper = new MachineHelper(lexCompare());
        expect(helper).toAdvanceTo(
            { channel: 'cmp', data: null },
            { channel: 'inner/left/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/result', data: '=' },
            { channel: 'inner/right/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/right/result', data: '=' },
            { channel: 'result', data: '=' }
        );
    });

    it('should handle multiple comparisons', () => {
        const helper = new MachineHelper(lexCompare());
        expect(helper).toAdvanceTo(
            { channel: 'cmp', data: null },
            { channel: 'inner/left/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/result', data: '<' },
            { channel: 'result', data: '<' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'cmp', data: null },
            { channel: 'inner/left/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/result', data: '=' },
            { channel: 'inner/right/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/right/result', data: '>' },
            { channel: 'result', data: '>' }
        );
        expect(helper).toAdvanceTo(
            { channel: 'cmp', data: null },
            { channel: 'inner/left/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/left/result', data: '=' },
            { channel: 'inner/right/cmp', data: null }
        );
        expect(helper).toAdvanceTo(
            { channel: 'inner/right/result', data: '=' },
            { channel: 'result', data: '=' }
        );
    });
});

function nameCompare(): Machine {
    return {
        start(): any {
            return { kind: 'start' };
        },
        advance(s: any, i: Input): [any, Output] {
            return [s, { channel: 'result', data: null }];
        },
    }
}