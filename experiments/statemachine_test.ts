import { assert } from "console";
import path from "path";
import { Context } from "vm";

declare global {
    namespace jest {
        interface Matchers<R> {
            toMatchTranscript(transcript: string[]): R;
        }
    }
}

type MachineImpl = {
    kind: 'emit',
    token: string,
} | {
    kind: 'choice',
    choices: Record<string, MachineImpl>
} | {
    kind: 'hidden',
    impl(state: any): any
} | {
    kind: 'sequence',
    inner: MachineImpl[]
} | {
    kind: 'product',
    inner: Record<string, MachineImpl>,
}

// Helper used in tests: a hidden machine that turns any context into a
// pair [newCtx, outputData] suitable for driving emit machines.
const wrapCtxAsPair: MachineImpl = {
    kind: 'hidden',
    impl: (ctx: any) => [ctx, {}],
};

type MachineImplState = {
    kind: 'hidden' 
    result: any,
} | {
    kind: 'emit',
    complete: boolean,
    ctx: any,
} | {
    kind: 'choice',
    chosen: false,
    ctx: any,
} | {
    kind: 'choice',
    chosen: true,
    choice: string,
    inner: MachineImplState,
} | {
    kind: 'sequence',
    done: false,
    idx: number,
    inner: MachineImplState,
} | {
    kind: 'sequence',
    done: true,
    ctx: any,
} | {
    kind: 'product',
    inner: Record<string, MachineImplState>,
};

function invalidMachineType(m: never): never {
    throw new Error('Invalid machine type: ' + JSON.stringify(m));
}

function liveMachine(m: MachineImpl) : Machine<MachineImplState, any, any> {
    return {
        start(ctx: any): MachineImplState {
            if (m.kind === 'emit') {
                return {kind: 'emit', complete: false, ctx};
            }
            if (m.kind === 'choice') {
                return {kind: 'choice', chosen: false, ctx};
            }
            if (m.kind === 'hidden') {
                return {kind: 'hidden', result: m.impl(ctx)};
            }
            if (m.kind === 'sequence') {
                if (m.inner.length === 0) {
                    return {kind: 'sequence', done: true, ctx};
                } else {
                    return {
                        kind: 'sequence',
                        done: false,
                        idx: 0,
                        inner: liveMachine(m.inner[0]).start(ctx),
                    };
                }
            }
            if (m.kind === 'product') {
                const innerStates: Record<string, MachineImplState> = {};
                for (const [channel, inner] of Object.entries(m.inner)) {
                    innerStates[channel] = liveMachine(inner).start(ctx);
                }
                return { kind: 'product', inner: innerStates };
            }
            invalidMachineType(m);
        },
        isComplete(s: MachineImplState): boolean {
            if (m.kind === 'hidden') {
                return true;
            }
            if (m.kind === 'emit') {
                if (s.kind !== 'emit') {
                    throw new Error('Expected emit state, got ' + JSON.stringify(s));
                }
                return s.complete;
            }
            if (m.kind === 'choice') {
                if (s.kind !== 'choice') {
                    throw new Error('Expected choice state, got ' + JSON.stringify(s));
                }
                if (s.chosen) {
                    return liveMachine(m.choices[s.choice]).isComplete(s.inner);
                } else {
                    return false;
                }
            }
            if (m.kind === 'sequence') {
                if (s.kind !== 'sequence') {
                    throw new Error('Expected sequence state, got ' + JSON.stringify(s));
                }
                return s.done;
            }
            if (m.kind === 'product') {
                if (s.kind !== 'product') {
                    throw new Error('Expected product state, got ' + JSON.stringify(s));
                }
                for (const [channel, inner] of Object.entries(m.inner)) {
                    if (!liveMachine(inner).isComplete(s.inner[channel])) {
                        return false;
                    }
                }
                return true;
            }
            invalidMachineType(m);
        },
        getResult(s: MachineImplState): any {
            if (m.kind === 'hidden') {
                if (s.kind !== 'hidden') {
                    throw new Error('Expected hidden state, got ' + JSON.stringify(s));
                }
                return s.result;
            }
            if (m.kind === 'emit') {
                if (s.kind !== 'emit') {
                    throw new Error('Expected emit state, got ' + JSON.stringify(s));
                }
                if (!s.complete) {
                    throw new Error('Emit state not complete');
                }
                return s.ctx;
            }
            if (m.kind === 'choice') {
                if (s.kind !== 'choice') {
                    throw new Error('Expected choice state, got ' + JSON.stringify(s));
                }
                if (!s.chosen) {
                    throw new Error('Choice state not chosen');
                }
                if (!liveMachine(m.choices[s.choice]).isComplete(s.inner)) {
                    throw new Error('Choice state not complete');
                }
                return liveMachine(m.choices[s.choice]).getResult(s.inner);
            }
            if (m.kind === 'sequence') {
                if (s.kind !== 'sequence') {
                    throw new Error('Expected sequence state, got ' + JSON.stringify(s));
                }
                if (!s.done) {
                    throw new Error('Sequence state not done');
                }
                return s.ctx;
            }
            if (m.kind === 'product') {
                if (s.kind !== 'product') {
                    throw new Error('Expected product state, got ' + JSON.stringify(s));
                }
                if (!this.isComplete(s)) {
                    throw new Error('Product state not complete');
                }
                const results: Record<string, any> = {};
                for (const [channel, inner] of Object.entries(m.inner)) {
                    results[channel] = liveMachine(inner).getResult(s.inner[channel]);
                }
                return results;
            }
            invalidMachineType(m);
        },
        readyForInput(s: MachineImplState): string[] {
            if (m.kind === 'hidden') {
                return [];
            }
            if (m.kind === 'emit') {
                return [];
            }
            if (m.kind === 'choice') {
                if (s.kind !== 'choice') {
                    throw new Error('Expected choice state, got ' + JSON.stringify(s));
                }
                if (s.chosen) {
                    return liveMachine(m.choices[s.choice]).readyForInput(s.inner);
                } else {
                    return Object.keys(m.choices);
                }
            }
            if (m.kind === 'sequence') {
                if (s.kind !== 'sequence') {
                    throw new Error('Expected sequence state, got ' + JSON.stringify(s));
                }
                if (s.done === true) {
                    return [];
                }
                return liveMachine(m.inner[s.idx]).readyForInput(s.inner);
            }
            if (m.kind === 'product') {
                if (s.kind !== 'product') {
                    throw new Error('Expected product state, got ' + JSON.stringify(s));
                }
                const channels: string[] = [];
                for (const [prefix, inner] of Object.entries(m.inner)) {
                    const innerState = s.inner[prefix];
                    const ready = liveMachine(inner).readyForInput(innerState);
                    for (const ch of ready) {
                        channels.push(`${prefix}/${ch}`);
                    }
                }
                return channels;
            }
            invalidMachineType(m);
        },
        sendInput (s, channel, data): MachineImplState {
            if (m.kind === 'hidden') {
                throw new Error('Hidden state does not accept input');
            }
            if (m.kind === 'emit') {
                throw new Error('Emit state does not accept input');
            }
            if (m.kind === 'choice') {
                if (s.kind !== 'choice') {
                    throw new Error('Expected choice state, got ' + JSON.stringify(s));
                }
                if (s.chosen === true) {
                    return liveMachine(m.choices[s.choice]).sendInput(s.inner, channel, data);
                } else {
                    if (m.choices[channel] === undefined) {
                        throw new Error(`Choice state does not have a branch for channel '${channel}'`);
                    }
                    return {
                        kind: 'choice', 
                        chosen: true, 
                        choice: channel, 
                        inner: liveMachine(m.choices[channel]).start([s.ctx, data]),
                    };
                }
            }
            if (m.kind === 'sequence') {
                if (s.kind !== 'sequence') {
                    throw new Error('Expected sequence state, got ' + JSON.stringify(s));
                }
                if (s.done === true) {
                    throw new Error('Sequence state is done');
                }
                const newInnerState = liveMachine(m.inner[s.idx]).sendInput(s.inner, channel, data);
                return {...s, inner: newInnerState};
            }
            if (m.kind === 'product') {
                if (s.kind !== 'product') {
                    throw new Error('Expected product state, got ' + JSON.stringify(s));
                }
                const slash = channel.indexOf('/');
                if (slash < 0) {
                    throw new Error(`Expected product channel 'prefix/sub', got '${channel}'`);
                }
                const prefix = channel.slice(0, slash);
                const innerChannel = channel.slice(slash + 1);
                const innerMachine = m.inner[prefix];
                if (innerMachine === undefined) {
                    throw new Error(`Product state does not have a branch for channel prefix '${prefix}'`);
                }
                const currentInnerState = s.inner[prefix];
                const newInnerState = liveMachine(innerMachine).sendInput(currentInnerState, innerChannel, data);
                return {
                    kind: 'product',
                    inner: {
                        ...s.inner,
                        [prefix]: newInnerState,
                    },
                };
            }
            invalidMachineType(m);
        },
        hasOutput(s: MachineImplState): string[] {
            if (m.kind === 'hidden') {
                return [];
            }
            if (m.kind === 'emit') {
                return [m.token];
            }
            if (m.kind === 'choice') {
                if (s.kind !== 'choice') {
                    throw new Error('Expected choice state, got ' + JSON.stringify(s));
                }
                if (s.chosen) {
                    return liveMachine(m.choices[s.choice]).hasOutput(s.inner);
                } else {
                    return [];
                }
            }
            if (m.kind === 'sequence') {
                if (s.kind !== 'sequence') {
                    throw new Error('Expected sequence state, got ' + JSON.stringify(s));
                }
                if (s.done === true) {
                    return [];
                }
                return liveMachine(m.inner[s.idx]).hasOutput(s.inner);
            }
            if (m.kind === 'product') {
                if (s.kind !== 'product') {
                    throw new Error('Expected product state, got ' + JSON.stringify(s));
                }
                const outputs: string[] = [];
                for (const [prefix, inner] of Object.entries(m.inner)) {
                    const innerState = s.inner[prefix];
                    const innerOutputs = liveMachine(inner).hasOutput(innerState);
                    for (const ch of innerOutputs) {
                        outputs.push(`${prefix}/${ch}`);
                    }
                }
                return outputs;
            }
            invalidMachineType(m);
        },
        getOutput(s: MachineImplState, channel: string): [MachineImplState, any] {
            if (m.kind === 'hidden') {
                throw new Error('Hidden state does not have output');
            }
            if (m.kind === 'emit') {
                if (s.kind !== 'emit') {
                    throw new Error('Expected emit state, got ' + JSON.stringify(s));
                }
                if (channel !== m.token) {
                    throw new Error(`Expected channel '${m.token}', got '${channel}'`);
                }
                // ctx is [newCtx, outputData]; emit outputData and store newCtx as ctx.
                if (!Array.isArray(s.ctx) || s.ctx.length !== 2) {
                    throw new Error('Emit ctx must be [newCtx, outputData]');
                }
                const [newCtx, outputData] = s.ctx;
                return [{ ...s, complete: true, ctx: newCtx }, outputData];
            }
            if (m.kind === 'choice') {
                if (s.kind !== 'choice') {
                    throw new Error('Expected choice state, got ' + JSON.stringify(s));
                }
                if (s.chosen) {
                    const [newInnerState, output] = liveMachine(m.choices[s.choice]).getOutput(s.inner, channel);
                    return [{...s, inner: newInnerState}, output];
                } else {
                    throw new Error('Choice state not chosen');
                }
            }
            if (m.kind === 'sequence') {
                if (s.kind !== 'sequence') {
                    throw new Error('Expected sequence state, got ' + JSON.stringify(s));
                }
                if (s.done === true) {
                    throw new Error('Sequence state is done');
                }
                const [newInnerState, output] = liveMachine(m.inner[s.idx]).getOutput(s.inner, channel);
                return [{...s, inner: newInnerState}, output];
            }
            if (m.kind === 'product') {
                if (s.kind !== 'product') {
                    throw new Error('Expected product state, got ' + JSON.stringify(s));
                }
                const slash = channel.indexOf('/');
                if (slash < 0) {
                    throw new Error(`Expected product channel 'prefix/sub', got '${channel}'`);
                }
                const prefix = channel.slice(0, slash);
                const innerChannel = channel.slice(slash + 1);
                const innerMachine = m.inner[prefix];
                if (innerMachine === undefined) {
                    throw new Error(`Product state does not have a branch for channel prefix '${prefix}'`);
                }
                const currentInnerState = s.inner[prefix];
                const [newInnerState, output] = liveMachine(innerMachine).getOutput(currentInnerState, innerChannel);
                return [
                    {
                        kind: 'product',
                        inner: {
                            ...s.inner,
                            [prefix]: newInnerState,
                        },
                    },
                    output,
                ];
            }
            invalidMachineType(m);
        },
        advance(s: MachineImplState): [MachineImplState, boolean] {
            if (m.kind === 'hidden') {
                return [s, false];
            }
            if (m.kind === 'emit') {
                return [s, false];
            }
            if (m.kind === 'choice') {
                if (s.kind !== 'choice') {
                    throw new Error('Expected choice state, got ' + JSON.stringify(s));
                }
                if (s.chosen) {
                    const [newInnerState, advanced] = liveMachine(m.choices[s.choice]).advance(s.inner);
                    return [{...s, inner: newInnerState}, advanced];
                } else {
                    return [s, false];
                }
            }
            if (m.kind === 'sequence') {
                if (s.kind !== 'sequence') {
                    throw new Error('Expected sequence state, got ' + JSON.stringify(s));
                }
                if (s.done === true) {
                    return [s, false];
                }
                const innerMachine = liveMachine(m.inner[s.idx]);
                if (innerMachine.isComplete(s.inner)) {
                    const ctx = innerMachine.getResult(s.inner);
                    if (s.idx === m.inner.length - 1) {
                        return [{kind: 'sequence', done: true, ctx}, true];
                    } else {
                        return [{
                            kind: 'sequence',
                            done: false,
                            idx: s.idx + 1,
                            inner: liveMachine(m.inner[s.idx + 1]).start(ctx),
                        }, true];
                    }
                } else {
                    const [newInnerState, advanced] = innerMachine.advance(s.inner);
                    return [{kind: 'sequence', done: false, idx: s.idx, inner: newInnerState}, advanced];
                }
            }
            if (m.kind === 'product') {
                if (s.kind !== 'product') {
                    throw new Error('Expected product state, got ' + JSON.stringify(s));
                }
                for (const [prefix, inner] of Object.entries(m.inner)) {
                    const innerState = s.inner[prefix];
                    const innerMachine = liveMachine(inner);
                    const [newInnerState, advanced] = innerMachine.advance(innerState);
                    if (advanced) {
                        return [
                            {
                                kind: 'product',
                                inner: {
                                    ...s.inner,
                                    [prefix]: newInnerState,
                                },
                            },
                            true,
                        ];
                    }
                }
                return [s, false];
            }
            invalidMachineType(m);
        },
    };
}

describe('liveMachine', () => {
    describe('hidden machine', () => {
        it('immediately completes and returns result', () => {
            const m = liveMachine({
                kind: 'hidden',
                impl: (ctx: number) => ctx * 2,
            });
            const state = m.start(5);
            expect(state.kind).toBe('hidden');
            if (state.kind === 'hidden') {
                expect(state.result).toBe(10);
            }
            expect(m.isComplete(state)).toBe(true);
            expect(m.getResult(state)).toBe(10);
        });

        it('does not accept input', () => {
            const m = liveMachine({
                kind: 'hidden',
                impl: (ctx: any) => ctx,
            });
            const state = m.start({});
            expect(() => m.sendInput(state, 'any', 'data')).toThrow('Hidden state does not accept input');
        });

        it('has no output', () => {
            const m = liveMachine({
                kind: 'hidden',
                impl: (ctx: any) => ctx,
            });
            const state = m.start({});
            expect(m.hasOutput(state)).toEqual([]);
            expect(() => m.getOutput(state, 'any')).toThrow('Hidden state does not have output');
        });

        it('does not advance', () => {
            const m = liveMachine({
                kind: 'hidden',
                impl: (ctx: any) => ctx,
            });
            const state = m.start({});
            const [newState, advanced] = m.advance(state);
            expect(advanced).toBe(false);
            expect(newState).toBe(state);
        });

        it('has no ready inputs', () => {
            const m = liveMachine({
                kind: 'hidden',
                impl: (ctx: any) => ctx,
            });
            const state = m.start({});
            expect(m.readyForInput(state)).toEqual([]);
        });
    });

    describe('emit machine', () => {
        it('starts incomplete', () => {
            const m = liveMachine({
                kind: 'emit',
                token: 'hello',
            });
            const state = m.start({ value: 42 });
            expect(state.kind).toBe('emit');
            if (state.kind === 'emit') {
                expect(state.complete).toBe(false);
                expect(state.ctx).toEqual({ value: 42 });
            }
            expect(m.isComplete(state)).toBe(false);
        });

        it('has output channel', () => {
            const m = liveMachine({
                kind: 'emit',
                token: 'hello',
            });
            const state = m.start({});
            expect(m.hasOutput(state)).toEqual(['hello']);
        });

        it('does not accept input', () => {
            const m = liveMachine({
                kind: 'emit',
                token: 'hello',
            });
            const state = m.start({});
            expect(() => m.sendInput(state, 'any', 'data')).toThrow('Emit state does not accept input');
        });

        it('getOutput splits ctx into result and output for emit machine', () => {
            const m = liveMachine({
                kind: 'emit',
                token: 'hello',
            });
            // For emit machines, ctx is [newCtx, outputData].
            const state = m.start([{ value: 7 }, { value: 42 }]);
            const [newState, output] = m.getOutput(state, 'hello');
            expect(output).toEqual({ value: 42 });
            // State changes - emit is marked as complete after output is consumed
            expect(newState.kind).toBe('emit');
            if (newState.kind === 'emit') {
                expect(newState.complete).toBe(true);
                expect(newState.ctx).toEqual({ value: 7 });
                // getResult returns the new context
                expect(m.getResult(newState)).toEqual({ value: 7 });
            }
        });

        it('getOutput throws error for wrong channel', () => {
            const m = liveMachine({
                kind: 'emit',
                token: 'hello',
            });
            const state = m.start({});
            expect(() => m.getOutput(state, 'wrong')).toThrow("Expected channel 'hello', got 'wrong'");
        });

        it('does not advance', () => {
            const m = liveMachine({
                kind: 'emit',
                token: 'hello',
            });
            const state = m.start({});
            const [newState, advanced] = m.advance(state);
            expect(advanced).toBe(false);
            expect(newState).toBe(state);
        });

        it('has no ready inputs', () => {
            const m = liveMachine({
                kind: 'emit',
                token: 'hello',
            });
            const state = m.start({});
            expect(m.readyForInput(state)).toEqual([]);
        });

        it('returns context as result when complete', () => {
            const m = liveMachine({
                kind: 'emit',
                token: 'hello',
            });
            const state = m.start([{ value: 1 }, { value: 2 }]);
            const [newState] = m.getOutput(state, 'hello');
            expect(m.getResult(newState)).toEqual({ value: 1 });
        });
    });

    describe('choice machine', () => {
        it('starts with no choice made', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'a': { kind: 'hidden', impl: (ctx: any) => ctx },
                    'b': { kind: 'hidden', impl: (ctx: any) => ctx },
                },
            });
            const state = m.start({ value: 1 });
            expect(state.kind).toBe('choice');
            if (state.kind === 'choice' && state.chosen === false) {
                expect(state.chosen).toBe(false);
                expect(state.ctx).toEqual({ value: 1 });
            }
            expect(m.isComplete(state)).toBe(false);
        });

        it('lists available choices as ready inputs', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'option1': { kind: 'hidden', impl: (ctx: any) => ctx },
                    'option2': { kind: 'hidden', impl: (ctx: any) => ctx },
                    'option3': { kind: 'hidden', impl: (ctx: any) => ctx },
                },
            });
            const state = m.start({});
            const ready = m.readyForInput(state);
            expect(ready.sort()).toEqual(['option1', 'option2', 'option3'].sort());
        });

        it('accepts input to choose a branch', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    // Choice branches now see [outerCtx, inputData] as their context.
                    // Test that both pieces of information are available.
                    'a': { kind: 'hidden', impl: ([outer, input]: [number, number]) => outer + input },
                    'b': { kind: 'hidden', impl: ([outer, input]: [number, number]) => outer * input },
                },
            });
            const state = m.start(5);
            const newState = m.sendInput(state, 'a', 7);
            expect(newState.kind).toBe('choice');
            if (newState.kind === 'choice' && newState.chosen) {
                expect(newState.chosen).toBe(true);
                expect(newState.choice).toBe('a');
                expect(newState.inner.kind).toBe('hidden');
                if (newState.inner.kind === 'hidden') {
                    // 5 (outer ctx) + 7 (input data)
                    expect(newState.inner.result).toBe(12);
                }
            }
        });

        it('throws error for invalid choice', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'a': { kind: 'hidden', impl: (ctx: any) => ctx },
                },
            });
            const state = m.start({});
            expect(() => m.sendInput(state, 'invalid', undefined)).toThrow("Choice state does not have a branch for channel 'invalid'");
        });

        it('delegates to chosen branch after selection', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'emit': { kind: 'emit', token: 'output' },
                    // Hidden branch also sees [outerCtx, inputData]; return them as a pair.
                    'hidden': { kind: 'hidden', impl: (pair: any) => pair },
                },
            });
            const state = m.start({ ctx: 1 });
            const chosenState = m.sendInput(state, 'hidden', { data: 2 } as any);
            expect(m.isComplete(chosenState)).toBe(true);
            // Result should contain both the original ctx and the input data.
            expect(m.getResult(chosenState)).toEqual([{ ctx: 1 }, { data: 2 }]);
        });

        it('has no output when no choice made', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'a': { kind: 'emit', token: 'output' },
                },
            });
            const state = m.start({});
            expect(m.hasOutput(state)).toEqual([]);
        });

        it('delegates output to chosen branch', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'emit': { kind: 'emit', token: 'output' },
                    'hidden': { kind: 'hidden', impl: (ctx: any) => ctx },
                },
            });
            const state = m.start({});
            const chosenState = m.sendInput(state, 'emit', undefined);
            expect(m.hasOutput(chosenState)).toEqual(['output']);
        });

        it('throws error when getting output before choice', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'a': { kind: 'emit', token: 'output' },
                },
            });
            const state = m.start({});
            expect(() => m.getOutput(state, 'output')).toThrow('Choice state not chosen');
        });

        it('throws error when getting result before choice', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'a': { kind: 'hidden', impl: (ctx: any) => ctx },
                },
            });
            const state = m.start({});
            expect(() => m.getResult(state)).toThrow('Choice state not chosen');
        });

        it('throws error when getting result before inner is complete', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'emit': { kind: 'emit', token: 'output' },
                },
            });
            const state = m.start({});
            const chosenState = m.sendInput(state, 'emit', undefined);
            expect(() => m.getResult(chosenState)).toThrow('Choice state not complete');
        });

        it('advances inner machine when chosen', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'emit': { kind: 'emit', token: 'test' },
                },
            });
            const state = m.start({});
            const chosenState = m.sendInput(state, 'emit', undefined);
            const [newState, advanced] = m.advance(chosenState);
            expect(advanced).toBe(false); // emit machines don't advance
            // The new state should be a choice state with the same structure
            expect(newState).toHaveProperty('kind', 'choice');
            if (newState.kind === 'choice' && chosenState.kind === 'choice') {
                expect(newState.chosen).toBe(chosenState.chosen);
                if (newState.chosen === true && chosenState.chosen === true) {
                    expect(newState.choice).toBe(chosenState.choice);
                    expect(newState.inner).toEqual(chosenState.inner);
                }
            }
        });

        it('does not advance when no choice made', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'a': { kind: 'hidden', impl: (ctx: any) => ctx },
                },
            });
            const state = m.start({});
            const [newState, advanced] = m.advance(state);
            expect(advanced).toBe(false);
            expect(newState).toBe(state);
        });
    });

    describe('liveMachine with MachineHelper', () => {
        it('choice to emit machine works with MachineHelper', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'hello': { kind: 'emit', token: 'hello' },
                    'world': { kind: 'emit', token: 'world' },
                },
            });
            const helper = new MachineHelper(m, 42);
            helper.sendInput('hello', 7);
            // Emit branch sees [outerCtx, inputData] as its context, but only outputs inputData.
            expect(helper).toAdvanceTo('hello', 7);
        });

        it('choice to hidden machine works with MachineHelper', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'double': { kind: 'hidden', impl: (ctx: number) => ctx * 2 },
                },
            });
            const helper = new MachineHelper(m, 5);
            helper.sendInput('double', 5);
        });

        // Note: Nested choices with MachineHelper are complex because MachineHelper's
        // advance method expects output after a single input, but nested choices
        // require multiple inputs. The direct API tests cover nested choice functionality.

        it('multiple choices work with MachineHelper', () => {
            const m = liveMachine({
                kind: 'choice',
                choices: {
                    'a': { kind: 'emit', token: 'a' },
                    'b': { kind: 'emit', token: 'b' },
                    'c': { kind: 'emit', token: 'c' },
                },
            });
            const helper1 = new MachineHelper(m, 'ctx1');
            helper1.sendInput('a', 1);
            expect(helper1).toAdvanceTo('a', 1);

            const helper2 = new MachineHelper(m, 'ctx2');
            helper2.sendInput('b', 2);
            expect(helper2).toAdvanceTo('b', 2);

            const helper3 = new MachineHelper(m, 'ctx3');
            helper3.sendInput('c', 3);
            expect(helper3).toAdvanceTo('c', 3);
        });

        describe('sequence machines', () => {
            it('empty sequence completes immediately', () => {
                const m = liveMachine({
                    kind: 'sequence',
                    inner: [],
                });
                const helper = new MachineHelper(m, [{}, {}]);
                // Empty sequence has no externally visible behavior:
                // requesting any output should eventually fail.
                expect(() => (helper as any).getOutput('anything')).toThrow();
            });

            it('sequence of emit machines produces outputs in order', () => {
                const m = liveMachine({
                    kind: 'sequence',
                    inner: [
                        wrapCtxAsPair,
                        { kind: 'emit', token: 'first' },
                        wrapCtxAsPair,
                        { kind: 'emit', token: 'second' },
                        wrapCtxAsPair,
                        { kind: 'emit', token: 'third' },
                    ],
                });
                const helper = new MachineHelper(m, {});
                // First machine in sequence should produce output
                expect(helper).toAdvanceTo('first', {});
                // After getting first output, second should be available
                expect(helper).toAdvanceTo('second', {});
                // After getting second output, third should be available
                expect(helper).toAdvanceTo('third', {});
            });

            it('sequence with choice machines', () => {
                const m = liveMachine({
                    kind: 'sequence',
                    inner: [
                        { kind: 'choice', choices: { 'a': { kind: 'emit', token: 'a' } } },
                        { kind: 'choice', choices: { 'b': { kind: 'emit', token: 'b' } } },
                    ],
                });
                const helper = new MachineHelper(m, ['s', {}]);
                // First choice machine needs input
                helper.sendInput('a', 10);
                // Emit output is just the input data
                expect(helper).toAdvanceTo('a', 10);
                // Second choice machine needs input
                helper.sendInput('b', 20);
                expect(helper).toAdvanceTo('b', 20);
            });

            it('sequence with hidden machines', () => {
                const m = liveMachine({
                    kind: 'sequence',
                    inner: [
                        // Prepare ctx as a pair before hitting the emit.
                        wrapCtxAsPair,
                        { kind: 'emit', token: 'result' },
                    ],
                });
                const helper = new MachineHelper(m, {});
                // Hidden machine completes immediately; MachineHelper will advance through it
                // when we request output on 'result'.
                expect(helper).toAdvanceTo('result', {});
            });

            it('sequence with mixed machine types', () => {
                const m = liveMachine({
                    kind: 'sequence',
                    inner: [
                        wrapCtxAsPair,
                        { kind: 'emit', token: 'start' },
                        { kind: 'choice', choices: { 'middle': { kind: 'emit', token: 'middle' } } },
                        // Hidden prepares a pair [newCtx, outputData] for the final emit.
                        { kind: 'hidden', impl: (ctx: any) => [({ ...(Array.isArray(ctx) ? ctx[0] : ctx), processed: true }), {}] },
                        { kind: 'emit', token: 'end' },
                    ],
                });
                const helper = new MachineHelper(m, { base: true });
                // First emit
                // Default emit output is empty object; ctx ({ base: true }) is carried forward.
                expect(helper).toAdvanceTo('start', {});
                // Choice needs input
                helper.sendInput('middle', 1);
                expect(helper).toAdvanceTo('middle', 1);
                // Hidden completes immediately; MachineHelper will advance through it
                // when we request output on 'end'. Default emit output is {}.
                expect(helper).toAdvanceTo('end', {});
            });

            it('nested sequence works correctly', () => {
                const m = liveMachine({
                    kind: 'sequence',
                    inner: [
                        wrapCtxAsPair,
                        { kind: 'emit', token: 'outer-start' },
                        {
                            kind: 'sequence',
                            inner: [
                                wrapCtxAsPair,
                                { kind: 'emit', token: 'inner-1' },
                                wrapCtxAsPair,
                                { kind: 'emit', token: 'inner-2' },
                            ],
                        },
                        wrapCtxAsPair,
                        { kind: 'emit', token: 'outer-end' },
                    ],
                });
                const helper = new MachineHelper(m, {});
                // Outer start
                expect(helper).toAdvanceTo('outer-start', {});
                // Inner sequence first emit
                expect(helper).toAdvanceTo('inner-1', {});
                // Inner sequence second emit
                expect(helper).toAdvanceTo('inner-2', {});
                // Outer end
                expect(helper).toAdvanceTo('outer-end', {});
            });

            it('sequence with choice that leads to sequence', () => {
                const m = liveMachine({
                    kind: 'sequence',
                    inner: [
                        wrapCtxAsPair,
                        { kind: 'emit', token: 'first' },
                        {
                            kind: 'choice',
                            choices: {
                                'path1': {
                                    kind: 'sequence',
                                    inner: [
                                        wrapCtxAsPair,
                                        { kind: 'emit', token: 'path1-a' },
                                        wrapCtxAsPair,
                                        { kind: 'emit', token: 'path1-b' },
                                    ],
                                },
                                'path2': { kind: 'emit', token: 'path2-single' },
                            },
                        },
                        wrapCtxAsPair,
                        { kind: 'emit', token: 'last' },
                    ],
                });
                const helper = new MachineHelper(m, 'root');
                // First emit: default output {}
                expect(helper).toAdvanceTo('first', {});
                // Choice needs input; choose path1.
                helper.sendInput('path1', 100);
                // Path1 emits use default output {}.
                expect(helper).toAdvanceTo('path1-a', {});
                expect(helper).toAdvanceTo('path1-b', {});
                // Last emit again outputs default {}
                expect(helper).toAdvanceTo('last', {});
            });

            it('product of emit machines exposes prefixed outputs', () => {
                const m = liveMachine({
                    kind: 'product',
                    inner: {
                        left: { kind: 'emit', token: 'a' },
                        right: { kind: 'emit', token: 'b' },
                    },
                });
                const helper = new MachineHelper(m, [{ prod: true }, {}]);
                // Order doesn't matter; each prefixed channel should produce its own output.
                // Default emit outputs are empty objects; ctx ({ prod: true }) is carried forward.
                expect(helper).toAdvanceTo('left/a', {});
                expect(helper).toAdvanceTo('right/b', {});
            });

            it('product with choice inner machines uses prefixed input channels', () => {
                const m = liveMachine({
                    kind: 'product',
                    inner: {
                        left: {
                            kind: 'choice',
                            choices: {
                                pick: { kind: 'emit', token: 'L' },
                            },
                        },
                        right: { kind: 'emit', token: 'R' },
                    },
                });
                const helper = new MachineHelper(m, ['base', {}]);
                // Provide input for the left side using a prefixed channel.
                helper.sendInput('left/pick', 5);
                // Left emit outputs only the input data
                expect(helper).toAdvanceTo('left/L', 5);
                // Right side emit is independent.
                expect(helper).toAdvanceTo('right/R', {});
            });
        });
    });
});

// MachineType helpers, validators, and related tests have been moved to statemachine_types_test.ts

class MachineHelper {
    private state: any;
    constructor(private machine: Machine<any, any, any>, initialCtx: any) {
        this.state = machine.start(initialCtx);
    }
    sendInput(channel: string, data: any) {
        // Advance until the machine is ready to accept input on the given channel,
        // or it can no longer make progress.
        while (true) {
            const readyChannels = this.machine.readyForInput(this.state);
            if (readyChannels.includes(channel)) {
                this.state = this.machine.sendInput(this.state, channel, data);
                return;
            }

            const [newState, advanced] = this.machine.advance(this.state);
            if (!advanced) {
                throw new Error(
                    `Machine did not advance and is not ready for input on channel '${channel}'`,
                );
            }
            this.state = newState;
        }
    }

    getOutput(channel: string): any {
        // Advance until we either have output on the requested channel
        // or the machine can no longer make progress.
        while (true) {
            const availableOutputs = this.machine.hasOutput(this.state);
            if (availableOutputs.includes(channel)) {
                const [newState, output] = this.machine.getOutput(this.state, channel);
                this.state = newState;
                return output;
            }

            const [newState, advanced] = this.machine.advance(this.state);
            if (!advanced) {
                throw new Error(
                    `Machine did not advance and no output available on channel '${channel}'`,
                );
            }
            this.state = newState;
        }
    }
}

// Custom Jest matcher for MachineHelper
expect.extend({
    toAdvanceTo(received: MachineHelper, expectedChannel: string, expectedData: any) {
        const actualData = received.getOutput(expectedChannel);
        const pass = this.equals(actualData, expectedData);

        if (pass) {
            return {
                message: () =>
                    `Expected machine not to produce data ${this.utils.printExpected(expectedData)} on channel '${expectedChannel}'`,
                pass: true,
            };
        } else {
            return {
                message: () =>
                    `Expected machine to produce on channel '${expectedChannel}':\n` +
                    `  ${this.utils.printExpected(expectedData)}\n` +
                    `Received:\n` +
                    `  ${this.utils.printReceived(actualData)}`,
                pass: false,
            };
        }
    },
});

// TypeScript declarations for the custom matcher
declare global {
    namespace jest {
        interface Matchers<R> {
            toAdvanceTo(expectedChannel: string, expectedData: any): R;
        }
    }
}

export { };

type Machine<S, I, O> = {
    start(ctx: any): S;
    isComplete(s: S): boolean;
    getResult(s: S): any;

    readyForInput(s: S): string[];
    sendInput(s: S, channel: string, data: I): S;
    hasOutput(s: S): string[];
    getOutput(s: S, channel: string): [S, O];
    advance(s: S): [S, boolean];
}
