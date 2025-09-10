// Test file for experiments.ts
import assert from 'assert';
import { andThen, call, HandlerResult, Machine, Result, sequence, smuggle, Startable, transformer } from './experiments';

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
    expect([result_action, result_output]).toEqual([expected_action, expected_output]);
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

const str_iter = transformer(([[str, offset], msg]: [StrIterState, ['next' | 'clone']]): [StrIterState, boolean | string] => {
  if (msg[0] === 'next') {
    offset += 1;
    return [[str, offset], offset < str.length];
  }
  if (msg[0] === 'clone') {
    return [[str, offset], str[offset]];
  }
  throw Error('Bad msg: ' + msg[0]);
});

describe('StrIter', () => {
  test('should work with empty string', () => {
    const str_iter_state = assertTransforms(str_iter_init, '');
    assertTranscript(str_iter, [
      [[str_iter_state, ['next']], 'result', [['', 0], false]],
    ]);
  });

  test('should work with non-empty string', () => {
    let str_iter_state = assertTransforms(str_iter_init, 'foo');
    let [s, has_next] = assertTransforms(str_iter, [str_iter_state, ['next']]);
    expect(has_next).toEqual(true);
    let [s2, char] = assertTransforms(str_iter, [s, ['clone']]);
    expect(char).toEqual('f');
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

const handler = andThen(
  transformer(([action, iter_state, iter_msg]: [string, StrIterState, any]) =>
    [iter_state, iter_msg]),
  str_iter);

const string_iter_equals_inverse = sequence([
  transformer((s: string) => [s, s]),
  smuggle(str_iter_init),
  transformer(([s, iter_state]: [string, StrIterState]) =>
    [iter_state, s]),
  call(string_iter_equals, handler),
  transformer(([iter_state, result]: [StrIterState, StringIterEqualsState, boolean]) => result)]);

describe('StringIterEqualsInverse', () => {
  test('handler alone', () => {
    assertTranscript(handler, [
      [['iter', ['foo', -1], ['next']], 'result', [['foo', 0], true]],
    ]);
  });
  test('should work', () => {
    assertTranscript(string_iter_equals_inverse, [
      ['foo', 'result', true],
    ]);
  });
});

type RaiseState = ["start"] | ["await_raise"] | ["end"];
function raise(state: RaiseState, msg: any): Result<RaiseState> {
  if (state[0] === "start") {
    let [action, inner_msg] = msg;
    return {
      action: action,
      msg: inner_msg,
      resume_state: ["await_raise"],
    };
  }
  if (state[0] === "await_raise") {
    return {
      action: "result",
      msg: msg,
      resume_state: ["end"],
    };
  }
  throw Error('Bad state: ' + state[0]);
}

export type IfThenElseState<T, F> = ["start"] | ["then", Startable<T>] | ["else", Startable<F>];
function if_then_else<T, F>(then: Machine<Startable<T>>, els: Machine<Startable<F>>): Machine<IfThenElseState<T, F>> {
  return function if_then_else_impl(state: IfThenElseState<T, F>, msg: any): Result<IfThenElseState<T, F>> {
    if (state[0] === "start") {
      let [outer_state, cond] = msg;
      if (cond) {
        return {
          action: "continue",
          msg: outer_state,
          resume_state: ["then", ["start"]],
        };
      } else {
        return {
          action: "continue",
          msg: outer_state,
          resume_state: ["else", ["start"]],
        };
      }
    }
    if (state[0] === "then") {
      const result = then(state[1], msg);
      return {
        action: result.action,
        msg: result.msg,
        resume_state: ["then", result.resume_state],
      }
    }
    if (state[0] === "else") {
      const result = els(state[1], msg);
      return {
        action: result.action,
        msg: result.msg,
        resume_state: ["else", result.resume_state],
      };
    }
    throw Error('Bad state: ' + state[0]);
  };
}

const char_iter_from_str_iter = sequence([
  // msg
  transformer((msg: any) => {
    if (msg[0] !== "next") {
      throw Error("Bad msg: " + msg);
    }
    return ["iter", ["next"]];
  }),
  raise,
  transformer((has_next: any) => [null, has_next]),
  if_then_else(
    sequence([
      transformer((_: any) => ["iter", ["clone"]]),
      raise,
      transformer((char: any) => ["some", char]),
    ]),
    sequence([
      transformer((_: any) => ["none"]),
    ]),
  )
]);

describe('CharIterFromStrIter', () => {
  test('unbound with empty string', () => {
    assertTranscript(char_iter_from_str_iter, [
      [['next'], 'iter', ['next']],
      [false, 'result', ['none']],
    ]);
  });
  test('unbound with non-empty string', () => {
    assertTranscript(char_iter_from_str_iter, [
      [['next'], 'iter', ['next']],
      [true, 'iter', ['clone']],
      ['f', 'result', ['some', 'f']],
    ]);
  });
});

