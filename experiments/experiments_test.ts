// Test file for experiments.ts
import assert from 'assert';
import { andThen, call, HandlerResult, Machine, Result, transformer } from './experiments';

function handleContinue<S>(machine: Machine<S>, state: S, input: any): [S, string, any] {
  let result = machine(state, input);
  while (result.action === 'continue') {
    state = result.resume_state;
    result = machine(state, result.msg);
  }
  return [result.resume_state, result.action, result.msg];
}

function assertTransforms(machine: Machine<any>, input: any): any {
  const result = machine(['start'], input);
  expect(result.action).toEqual('result');
  return result.msg;
}

function assertTranscript(machine: Machine<any>, transcript: [any, string, any][], state: any = null) {
  state = state || ['start'];
  let i = 0;
  for (const [input, expected_action, expected_output] of transcript) {
    console.log(`${i}: ${input} -> ${expected_action} ${expected_output}`);
    const [new_state, result_action, result_output] = handleContinue(machine, state, input);
    expect(result_action).toEqual(expected_action);
    expect(result_output).toEqual(expected_output);
    state = new_state;
    i++;
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

function str_iter([str, offset]: StrIterState, msg: ['next' | 'clone']): Result<StrIterState> {
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
  throw Error('Bad msg: ' + msg[0]);
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

type StringIterEqualsState = ["start"] | ["await_next", string] | ["await_clone", string] | ["end"];


function string_iter_equals(state: StringIterEqualsState, msg: any): Result<StringIterEqualsState> {
  if (state[0] === "start") {
    const s = msg;
    return {
      action: "iter",
      msg: ["next"],
      resume_state: ["await_next", s],
    };
  }
  if (state[0] === "await_next") {
    const s = state[1];
    const iter_has_next = msg;
    const str_has_next = s.length > 0;
    if (iter_has_next && str_has_next) {
      return {
        action: "iter",
        msg: ["clone"],
        resume_state: ["await_clone", s],
      };
    }
    if (!iter_has_next && !str_has_next) {
      return {
        action: "result",
        msg: true,
        resume_state: ["end"],
      };
    }
    // Otherwise: !iter_has_next || !str_has_next
    return {
      action: "result",
      msg: false,
      resume_state: ["end"],
    };
  }
  if (state[0] === "await_clone") {
    const s = state[1];
    const iter_char = msg;
    const str_char = s[0];
    if (iter_char === str_char) {
      return {
        action: "continue",
        msg: s.slice(1),
        resume_state: ["start"],
      };
    } else {
      return {
        action: "result",
        msg: false,
        resume_state: ["end"],
      };
    }
  }
  throw Error('Bad state: ' + state[0]);
}

describe('StringIterEquals', () => {
  test('should work with empty string', () => {
    assertTranscript(string_iter_equals, [
      ['', 'iter', ['next']],
      [false, 'result', true],
    ]);
  });

  test('should work with non-empty string', () => {
    assertTranscript(string_iter_equals, [
      ['foo', 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['f', 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['o', 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['o', 'iter', ['next']],
      [false, 'result', true],
    ]);
  });

  test('should work with iter shorter than string', () => {
    assertTranscript(string_iter_equals, [
      ['foo', 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['f', 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['o', 'iter', ['next']],
      [false, 'result', false],
    ]);
  });

  test('should work with string shorter than iter', () => {
    assertTranscript(string_iter_equals, [
      ['foo', 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['f', 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['o', 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['o', 'iter', ['next']],
      [true, 'result', false],
    ]);
  });

  test('should work with char mismatch', () => {
    assertTranscript(string_iter_equals, [
      ['foo', 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['f', 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['r', 'result', false],
    ]);
  });
});

function passThroughHandler<S>(handler_name: string, state: S, msg: any): HandlerResult<S> {
  return { kind: "continue", action: handler_name, msg: msg, handler_state: state };
}

function nullHandlerMachine(state: ["start"], msg: any): Result<["start"]> {
  throw Error('Bad state: ' + state[0]);
}

type RandomHandlerState = ["start" | "end"] | ["iter", StrIterState];

const string_iter_equals_inverse = andThen(andThen(andThen(andThen(
  transformer((s: string) => [s, ["start"], s]),
  call(str_iter_init, nullHandlerMachine)),
  transformer(([s, constructor_state, iter_state]: [string, ["start"], StrIterState]) =>
    [iter_state, ["start"], s])),
  call(string_iter_equals, (s: RandomHandlerState, msg): Result<RandomHandlerState> => {
    if (s[0] === "start") {
      let [action, iter_state, iter_msg] = msg;
      if (action !== "iter") {
        throw Error('Bad action: ' + action);
      }
      return { action: "continue", msg: iter_msg, resume_state: ["iter", iter_state] };
    }
    if (s[0] === "iter") {
      let iter_state = s[1];
      const result = str_iter(iter_state, msg);
      if (result.action === "result") {
        return { action: "result", msg: [result.resume_state, result.msg], resume_state: ["end"] };
      } else {
        return { action: result.action, msg: result.msg, resume_state: ["iter", result.resume_state] };
      }
    }
    throw Error('Bad state: ' + s[0]);
  }
  )), transformer(([iter_state, iter_equals_state, result]: [StrIterState, StringIterEqualsState, boolean]) => result));


describe('StringIterEqualsInverse', () => {
  test('should work', () => {
    assertTranscript(string_iter_equals_inverse, [
      ['foo', 'result', true],
    ]);
  });
});