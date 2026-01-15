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

    // Takes a state and returns a string if the state is terminal, indicating 
    // which terminus was reached. Otherwise, returns null.
    is_terminal(s: any): string | null;
}

// Test helper: runs a machine through a list of inputs and asserts the outputs match
function runMachine(machine: Machine, ioPairs: Array<{input: Input, output: Output}>): void {
    let state = machine.start();
    for (let i = 0; i < ioPairs.length; i++) {
        const {input, output: expectedOutput} = ioPairs[i];
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

function constant(channel_in: string, channel_out: string, data: any): Machine {
    return {
        start(): any {
            return null;
        },
        advance(s: any, i: Input): [any, Output] {
            if (i.channel !== channel_in) {
                throw new Error('Invalid channel: ' + i.channel);
            }
            return [s, {channel: channel_out, data: data}];
        },
        is_terminal(s: any): string | null {
            return channel_out;
        },
    }
}

describe('constant', () => {
    it('should throw an error if the channel is invalid', () => {
        const machine = constant('in', 'out', 'data');
        expect(() => machine.advance(null, {channel: 'invalid', data: 'data'})).toThrow('Invalid channel: invalid');
    });
    it('should return the data', () => {
        const machine = constant('in', 'out', 'data');
        const [state, output] = machine.advance(null, {channel: 'in', data: 'data'});
        expect(output).toEqual({channel: 'out', data: 'data'});
    });
    it('should handle multiple inputs correctly', () => {
        const machine = constant('in', 'out', 'data');
        runMachine(machine, [
            {input: {channel: 'in', data: 'input1'}, output: {channel: 'out', data: 'data'}},
            {input: {channel: 'in', data: 'input2'}, output: {channel: 'out', data: 'data'}},
            {input: {channel: 'in', data: 'input3'}, output: {channel: 'out', data: 'data'}},
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
                const [new_s2, o2] = m2.advance(s2, {channel: m2_channel, data: o1.data});
                return [[new_s1, new_s2], {channel: '2/' + o2.channel, data: o2.data}];
            } else {
                return [[new_s1, s2], {channel: '1/' + m1_channel, data: o1.data}];
            }
        },
        is_terminal([s1, s2]: [any, any]): string | null {
            const m1_terminal = m1.is_terminal(s1);
            if (m1_terminal !== null) {
                return '1/' + m1_terminal;
            }
            const m2_terminal = m2.is_terminal(s2);
            if (m2_terminal !== null) {
                return '2/' + m2_terminal;
            }
            return null;
        },
    }
}

describe('compose', () => {
    it('should return start states from both machines', () => {
        const m1 = constant('a', 'b', 'data1');
        const m2 = constant('c', 'd', 'data2');
        const composed = compose(m1, 'b', m2, 'c');
        const start = composed.start();
        expect(start).toEqual([null, null]);
    });

    it('should forward to m2 when m1 output matches m1_channel', () => {
        const m1 = constant('in', 'forward', 'data1');
        const m2 = constant('forward', 'out', 'data2');
        const composed = compose(m1, 'forward', m2, 'forward');
        const [state, output] = composed.advance([null, null], {channel: 'in', data: 'input'});
        expect(output).toEqual({channel: '2/out', data: 'data2'});
        expect(state).toEqual([null, null]);
    });

    it('should return m1 output when it does not match m1_channel', () => {
        const m1 = constant('in', 'other', 'data1');
        const m2 = constant('forward', 'out', 'data2');
        const composed = compose(m1, 'forward', m2, 'forward');
        const [state, output] = composed.advance([null, null], {channel: 'in', data: 'input'});
        expect(output).toEqual({channel: '1/forward', data: 'data1'});
        expect(state).toEqual([null, null]);
    });

    it('should pass m1 output data to m2 when forwarding', () => {
        const m1 = constant('in', 'forward', 'data_from_m1');
        const m2 = constant('forward', 'out', 'data2');
        const composed = compose(m1, 'forward', m2, 'forward');
        const [state, output] = composed.advance([null, null], {channel: 'in', data: 'input'});
        // m2 should receive 'data_from_m1' as input data
        expect(output).toEqual({channel: '2/out', data: 'data2'});
    });

    it('should correctly identify terminal state for m1 channel', () => {
        const m1 = constant('a', 'b', 'data1');
        const m2 = constant('c', 'd', 'data2');
        const composed = compose(m1, 'b', m2, 'c');
        expect(composed.is_terminal([null, null])).toBe('1/b');
    });

    it('should correctly identify terminal state for m2 channel', () => {
        const m1 = constant('in', 'out', 'data1');
        const m2 = constant('in', 'out', 'data2');
        const composed = compose(m1, 'out', m2, 'in');
        expect(composed.is_terminal([null, null])).toBe('1/out');
    });
});

// Runs a until it is terminal, then runs the matching b from b_map.
function sequence(a: Machine, b_map: Record<string, Machine>): Machine {
    return {
        start(): [any, string | null, any] {
            return [a.start(), null, null];
        },
        advance([sa, b_key, sb]: [any, string | null, any], i: Input): [any, Output] {
            if (b_key === null) {
                // In A phase
                const [new_sa, oa] = a.advance(sa, i);
                // Check if A is terminal and transition to matching B
                const terminus = a.is_terminal(new_sa);
                if (terminus !== null && terminus in b_map) {
                    const b = b_map[terminus];
                    const b_start = b.start();
                    return [[new_sa, terminus, b_start], {channel: oa.channel, data: oa.data}];
                } else {
                    // Stay in A phase if not terminal or no matching B
                    return [[new_sa, null, null], {channel: oa.channel, data: oa.data}];
                }
            } else {
                // In B phase, send input to current B machine
                const b = b_map[b_key];
                const [new_sb, ob] = b.advance(sb, i);
                return [[sa, b_key, new_sb], {channel: ob.channel, data: ob.data}];
            }
        },
        is_terminal([sa, b_key, sb]: [any, string | null, any]): string | null {
            if (b_key === null) {
                return a.is_terminal(sa);
            } else {
                const b = b_map[b_key];
                return b.is_terminal(sb);
            }
        },
    }
}

describe('sequence', () => {
    it('should start in A phase', () => {
        const a = constant('in', 'out', 'data1');
        const b = constant('in', 'out', 'data2');
        const seq = sequence(a, {'out': b});
        const start = seq.start();
        expect(start).toEqual([null, null, null]);
    });

    it('should send inputs to A and return A outputs until A is terminal', () => {
        const a = constant('in', 'other', 'data1');
        const b = constant('in', 'out', 'data2');
        const seq = sequence(a, {'other': b});
        let state = seq.start();
        const [newState, output] = seq.advance(state, {channel: 'in', data: 'input'});
        expect(output).toEqual({channel: 'other', data: 'data1'});
        expect(newState).toEqual([null, 'other', null]);
    });

    it('should transition to B phase when A is terminal', () => {
        const a = constant('in', 'trigger', 'data1');
        const b = constant('in', 'out', 'data2');
        const seq = sequence(a, {'trigger': b});
        let state = seq.start();
        const [newState, output] = seq.advance(state, {channel: 'in', data: 'input'});
        expect(output).toEqual({channel: 'trigger', data: 'data1'});
        expect(newState).toEqual([null, 'trigger', null]);
    });

    it('should send subsequent inputs to B after transition', () => {
        const a = constant('in', 'trigger', 'data1');
        const b = constant('in', 'out', 'data2');
        const seq = sequence(a, {'trigger': b});
        let state = seq.start();
        // First input: triggers transition
        const [newState1, output1] = seq.advance(state, {channel: 'in', data: 'input1'});
        expect(output1.channel).toBe('trigger');
        state = newState1;
        // Second input: should go to B
        const [newState, output] = seq.advance(state, {channel: 'in', data: 'input2'});
        expect(output).toEqual({channel: 'out', data: 'data2'});
        expect(newState).toEqual([null, 'trigger', null]);
    });

    it('should correctly identify terminal state for A phase', () => {
        const a = constant('a', 'b', 'data1');
        const b = constant('c', 'd', 'data2');
        const seq = sequence(a, {'b': b});
        expect(seq.is_terminal([null, null, null])).toBe('b');
    });

    it('should correctly identify terminal state for B phase', () => {
        const a = constant('a', 'b', 'data1');
        const b = constant('c', 'd', 'data2');
        const seq = sequence(a, {'b': b});
        expect(seq.is_terminal([null, 'b', null])).toBe('d');
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
            return ['end', {channel: 'result', data: f(i.data)}];
        },
        is_terminal(s: any): string | null {
            if (s === 'start') {
                return null;
            }
            if (s === 'end') {
                return 'exit';
            }
            throw new Error('Invalid state: ' + s);
        },
    }
}
function yld(channel:string): Machine {
    return {
        start(): any {
            return 'start';
        },
        advance(s: any, i: Input): [any, Output] {
            if (s === 'start') {
                if (i.channel !== "result") {
                    throw new Error('Invalid channel: ' + i.channel);
                }
                return ['awaiting', {channel, data: i.data}];
            }
            if (s === 'awaiting') {
                if (i.channel !== channel) {
                    throw new Error('Invalid channel: ' + i.channel);
                }
                return ['end', {channel: "result", data: i.data}];
            }
            throw new Error('Invalid state: ' + s);
        },
        is_terminal(s: any): string | null {
            if (s === 'start') {
                return null;
            }
            if (s === 'awaiting') {
                return null;
            }
            if (s === 'end') {
                return 'exit';
            }
            throw new Error('Invalid state: ' + s);
        },
    }
}

function stash(inner: Machine): Machine {
    return {
        start(): any {
            return {kind: 'start'};
        },
        advance(s: any, i: Input): [any, Output] {
            if (s.kind === 'start') {
                if (i.channel !== 'result') {
                    throw new Error('Invalid channel: ' + i.channel);
                }
                let [new_inner, output] = inner.advance(inner.start(), {channel: 'result', data: i.data[1]});

                if (inner.is_terminal(new_inner) !== null) {
                    return [{kind: 'end'}, {channel: 'result', data: [i.data[0], output.data]}];
                }
                return [{kind: 'running', stashed: i.data[0], inner: new_inner}, output];
            }
            if (s.kind === 'running') {
                let [new_inner, output] = inner.advance(s.inner, i);
                if (inner.is_terminal(new_inner) !== null) {
                    return [{kind: 'end'}, {channel: 'result', data: [s.stashed, output.data]}];
                }
                return [{kind: 'running', stashed: s.stashed, inner: new_inner}, output];
            }
            throw new Error('Invalid state: ' + s);
        },
        is_terminal(s: any): string | null {
            if (s.kind === 'start') {
                return null;
            }
            if (s.kind === 'running') {
                return null;
            }
            if (s.kind === 'end') {
                return 'exit';
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
            while (!machine.is_terminal(s)) {
                const [new_s, output] = machine.advance(s, i);
                if (output.channel !== 'result') {
                    return [new_s, output];
                }
                s = new_s;
                i = {channel: 'result', data: output.data};
            }
            return [s, i]
        },
        is_terminal(s: any): string | null {
            return machine.is_terminal(s);
        },
    }
}

describe('yld', () => {
    it('func with yld', () => {
        const f = func((x: any) => [x + 1, 'hello world']);
        const y = yld('channel');
        const g = func(([x, y]: [number, string]) => '' + y + "/" + x);
        const machine = sequence(f, {exit: sequence(stash(y), {exit: g})});
        runMachine(machine, [
            {input: {channel: 'result', data: 4}, output: {channel: 'result', data: [5, 'hello world']}},
            {input: {channel: 'result', data: [5, 'hello world']}, output: {channel: 'channel', data: 'hello world'}},
            {input: {channel: 'channel', data: 'my guy'}, output: {channel: 'result', data: [5, 'my guy']}},
            {input: {channel: 'result', data: [5, 'my guy']}, output: {channel: 'result', data: 'my guy/5'}},
        ]);
    });

    it('func with yld pipelined', () => {
        const f = func((x: any) => [x + 1, 'hello world']);
        const y = yld('channel');
        const g = func(([x, y]: [number, string]) => '' + y + "/" + x);
        const machine = pipeline(sequence(f, {exit: sequence(stash(y), {exit: g})}));
        runMachine(machine, [   
            {input: {channel: 'result', data: 4}, output: {channel: 'channel', data: 'hello world'}},
            {input: {channel: 'channel', data: 'my guy'}, output: {channel: 'result', data: 'my guy/5'}},
        ]);
    });
});