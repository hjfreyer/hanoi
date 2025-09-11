// Test file for experiments.ts
import assert from 'assert';
import { andThen, call, closure, HandlerResult, if_then_else, Machine, match, raise, Result, sequence, smuggle, Startable, transformer } from './experiments';

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

type SSVIterState = ["start"] | ["in_field", ["some", string] | ["none"]] | ["almost_finished"] | ["end"];

const space_separated_value = sequence([
  transformer(([state, msg]: [SSVIterState, any]) =>
    [[state, msg], state[0]]
  ),
  match({
    start:
      transformer(([state, msg]: [SSVIterState, any]) => {
        if (msg[0] !== "next") {
          throw Error("Bad msg: " + msg);
        }
        return [["in_field", ["none"]], true];
      }),
    in_field: sequence([
      transformer(([state, msg]: [SSVIterState, any]) =>
        [state, msg[0]]
      ),
      match({
        inner_next:
          sequence([
            transformer((state: SSVIterState) =>
              ["iter", ["next"]]
            ),
            raise,
            transformer((next_char: ["some", string] | ["none"]) => [next_char, next_char[0] === "some"]),
            if_then_else(
              sequence([
                transformer(([_, char]: ["some", string]) => [char, char === " "]),
                if_then_else(
                  transformer((_: any) => [["start"], false]),
                  transformer((char: string) => [["in_field", ["some", char]], true]),
                ),
              ]),
              transformer(([_]: ["none"]) => [["almost_finished"], false]),
            ),
          ]),
        inner_clone:
          transformer((state: SSVIterState) => {
            if (state[0] !== "in_field") {
              throw Error("Bad state: " + state);
            }
            if (state[1][0] !== "some") {
              throw Error("Bad state: " + state);
            }
            return [state, state[1][1]];
          }),
      }),
    ]),
    almost_finished:
      transformer(([state, msg]: [SSVIterState, any]) => {
        if (msg[0] !== "next") {
          throw Error("Bad msg: " + msg);
        }
        return [["end"], false];
      }),
  }),
]);


describe('SpaceSeparatedValueAdvance', () => {
  const closed = closure(space_separated_value);
  test('empty string', () => {
    assertTranscript(closed, [
      [['start'], 'result', null],
      [['next'], 'result', true],
      [['inner_next'], 'iter', ['next']],
      [['none'], 'result', false],
      [['next'], 'result', false],
    ]);
  });
  test('one field', () => {
    assertTranscript(closed, [
      [['start'], 'result', null],
      [['next'], 'result', true],
      [['inner_next'], 'iter', ['next']],
      [['some', 'f'], 'result', true],
      [['inner_clone'], 'result', 'f'],
      [['inner_next'], 'iter', ['next']],
      [['some', 'o'], 'result', true],
      [['inner_next'], 'iter', ['next']],
      [['none'], 'result', false],
      [['next'], 'result', false],
    ]);
  });
  test('double field', () => {
    assertTranscript(closed, [
      [['start'], 'result', null],
      [['next'], 'result', true],
      [['inner_next'], 'iter', ['next']],
      [['some', 'f'], 'result', true],
      [['inner_next'], 'iter', ['next']],
      [['some', ' '], 'result', false],
      [['next'], 'result', true],
      [['inner_next'], 'iter', ['next']],
      [['some', 'o'], 'result', true],
      [['inner_next'], 'iter', ['next']],
      [['none'], 'result', false],
      [['next'], 'result', false],
    ]);
  });
});