// Test file for experiments.ts
import assert from 'assert';
import { Machine, transformer } from './experiments';


function assertTransforms(machine: Machine<any>, input: any): any {
  const result = machine(['start'], input);
  expect(result.action).toEqual('result');
  return result.msg;
}

function assertTranscript(machine: Machine<any>, transcript: [any, string, any][], state: any = null) {
  state = state || ['start'];
  for (const [input, expected_action, expected_output] of transcript) {
    const result = machine(state, input);
    expect(result.action).toEqual(expected_action);
    expect(result.msg).toEqual(expected_output);
    state = result.resume_state;
  }
}

describe('Transformer', () => {
  const machine = transformer(x => x + 1);
  test('should do the thing', () => {
    assertTranscript(machine, [
      [2, 'result', 3],
    ]);
  });
});

const str_iter_init = transformer((s: string) => [s, -1]);

type StrIterState = [string, number];

function str_iter([str, offset]: StrIterState, msg: ['next' | 'clone']) {
  if (msg[0] === 'next') {
    offset += 1;
    return {
      action: 'result',
      msg: offset < str.length,
      resume_state: [str, offset],
    };
  }
  if (msg[0] === 'clone') {
    return {
      action: 'result',
      msg: str[offset],
      resume_state: [str, offset],
    };
  }
  assert(false, 'Bad msg: ' + msg[0]);
}

describe('StrIter', () => {
  test('should work with empty string', () => {
    const str_iter_state = assertTransforms(str_iter_init, '');
    assertTranscript(str_iter, [
      [['next'], 'result', false],
    ], str_iter_state);
  });

  test('should work with non-empty string', () => {
    const str_iter_state = assertTransforms(str_iter_init, 'foo');
    assertTranscript(str_iter, [
      [['next'], 'result', true],
      [['clone'], 'result', 'f'],
      [['next'], 'result', true],
      [['clone'], 'result', 'o'],
      [['next'], 'result', true],
      [['clone'], 'result', 'o'],
      [['next'], 'result', false],
    ], str_iter_state);
  });
});