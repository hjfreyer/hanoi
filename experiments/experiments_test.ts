// Test file for experiments.ts
import assert from 'assert';
import { andThen, call, closure, HandlerResult, if_then_else, loop, Machine, match, raise, Result, sequence, smuggle, Startable, transformer } from './experiments';

function handleContinue<S>(machine: Machine<S>, state: S, input: any): [S, string, any] {
  let result = machine(state, input);
  while (result.action === 'continue') {
    state = result.resume_state;
    result = machine(state, result.msg);
  }
  return [result.resume_state, result.action, result.msg];
}

class Transcript {
  constructor(public machine: Machine<any>, public state: any = null) {
    this.machine = machine;
    this.state = state || ['start'];
  }

  assertNext(input: any, expected_action: string, expected_output: any) {
    const [new_state, result_action, result_output] = handleContinue(this.machine, this.state, input);
    expect([result_action, result_output]).toEqual([expected_action, expected_output]);
    this.state = new_state;
  }
}

function assertTransforms(machine: Machine<any>, input: any): any {
  const result = machine(['start'], input);
  expect(result.action).toEqual('result');
  return result.msg;
}


describe('Transformer', () => {
  const machine = transformer(x => x + 1);
  test('should do the thing', () => {
    const transcript = new Transcript(machine);
    transcript.assertNext(2, 'result', 3);
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
    const transcript = new Transcript(str_iter);
    transcript.assertNext([str_iter_state, ['next']], 'result', [['', 0], false]);
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
    const transcript = new Transcript(string_iter_equals);
    transcript.assertNext('', 'iter', ['next']);
    transcript.assertNext(false, 'result', true);
  });

  test('should work with non-empty string', () => {
    const transcript = new Transcript(string_iter_equals);
    transcript.assertNext('foo', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('o', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('o', 'iter', ['next']);
    transcript.assertNext(false, 'result', true);
  });

  test('should work with iter shorter than string', () => {
    const transcript = new Transcript(string_iter_equals);
    transcript.assertNext('foo', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('o', 'iter', ['next']);
    transcript.assertNext(false, 'result', false);
  });

  test('should work with string shorter than iter', () => {
    const transcript = new Transcript(string_iter_equals);
    transcript.assertNext('foo', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('o', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('o', 'iter', ['next']);
    transcript.assertNext(true, 'result', false);
  });

  test('should work with char mismatch', () => {
    const transcript = new Transcript(string_iter_equals);
    transcript.assertNext('foo', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('r', 'result', false);
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
    const transcript = new Transcript(handler);
    transcript.assertNext(['iter', ['foo', -1], ['next']], 'result', [['foo', 0], true]);
  });
  test('should work', () => {
    const transcript = new Transcript(string_iter_equals_inverse);
    transcript.assertNext('foo', 'result', true);
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
    const transcript = new Transcript(char_iter_from_str_iter);
    transcript.assertNext(['next'], 'iter', ['next']);
    transcript.assertNext(false, 'result', ['none']);
  });
  test('unbound with non-empty string', () => {
    const transcript = new Transcript(char_iter_from_str_iter);
    transcript.assertNext(['next'], 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'result', ['some', 'f']);
  });
});

type CharIterFromStringState = [string, number];
const char_iter_from_string_init = transformer((s: string) => [s, -1]);

const char_iter_from_string = sequence([
  transformer(([[s, offset], msg]: [CharIterFromStringState, any]) => {
    if (msg[0] !== "next") {
      throw Error("Bad msg: " + msg);
    }
    offset += 1;
    if (offset < s.length) {
      return [[s, offset], ["some", s[offset]]];
    }
    return [[s, offset], ["none"]];
  }),
]);

describe('CharIterFromString', () => {
  test('empty string', () => {
    const iter = assertTransforms(char_iter_from_string_init, '');
    expect(iter).toEqual(['', -1]);

    const transcript = new Transcript(closure(char_iter_from_string));
    transcript.assertNext(iter, 'result', null);
    transcript.assertNext(['next'], 'result', ['none']);
  });
  test('non-empty string', () => {
    const iter = assertTransforms(char_iter_from_string_init, 'foo');
    expect(iter).toEqual(['foo', -1]);

    const transcript = new Transcript(closure(char_iter_from_string));
    transcript.assertNext(iter, 'result', null);
    transcript.assertNext(['next'], 'result', ['some', 'f']);
    transcript.assertNext(['next'], 'result', ['some', 'o']);
    transcript.assertNext(['next'], 'result', ['some', 'o']);
    transcript.assertNext(['next'], 'result', ['none']);
  });
});

type SSVIterState = ["start"] | ["in_field"] | ["almost_finished"] | ["end"];

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
      transformer(([state, msg]: [SSVIterState, any]) => {
        if (msg[0] !== "inner_next") {
          throw Error("Bad msg: " + msg);
        }
        return ["iter", ["next"]];
      }),
      raise,
      transformer((next_char: ["some", string] | ["none"]) => [next_char, next_char[0] === "some"]),
      if_then_else(
        sequence([
          transformer(([_, char]: ["some", string]) => [char, char === " "]),
          if_then_else(
            transformer((_: any) => [["start"], ["none"]]),
            transformer((char: string) => [["in_field"], ["some", char]]),
          ),
        ]),
        transformer(([_]: ["none"]) => [["almost_finished"], ["none"]]),
      ),
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
    const transcript = new Transcript(closed);
    transcript.assertNext(['start'], 'result', null);
    transcript.assertNext(['next'], 'result', true);
    transcript.assertNext(['inner_next'], 'iter', ['next']);
    transcript.assertNext(['none'], 'result', ['none']);
    transcript.assertNext(['next'], 'result', false);
  });
  test('one field', () => {
    const transcript = new Transcript(closed);
    transcript.assertNext(['start'], 'result', null);
    transcript.assertNext(['next'], 'result', true);
    transcript.assertNext(['inner_next'], 'iter', ['next']);
    transcript.assertNext(['some', 'f'], 'result', ['some', 'f']);
    transcript.assertNext(['inner_next'], 'iter', ['next']);
    transcript.assertNext(['some', 'o'], 'result', ['some', 'o']);
    transcript.assertNext(['inner_next'], 'iter', ['next']);
    transcript.assertNext(['none'], 'result', ['none']);
    transcript.assertNext(['next'], 'result', false);
  });

  test('double field', () => {
    const transcript = new Transcript(closed);
    transcript.assertNext(['start'], 'result', null);
    transcript.assertNext(['next'], 'result', true);
    transcript.assertNext(['inner_next'], 'iter', ['next']);
    transcript.assertNext(['some', 'f'], 'result', ['some', 'f']);
    transcript.assertNext(['inner_next'], 'iter', ['next']);
    transcript.assertNext(['some', ' '], 'result', ['none']);
    transcript.assertNext(['next'], 'result', true);
    transcript.assertNext(['inner_next'], 'iter', ['next']);
    transcript.assertNext(['some', 'o'], 'result', ['some', 'o']);
    transcript.assertNext(['inner_next'], 'iter', ['next']);
    transcript.assertNext(['none'], 'result', ['none']);
    transcript.assertNext(['next'], 'result', false);
  });
});

const parse_int = sequence([
  transformer((msg: null) => {
    if (msg !== null) {
      throw Error("Bad msg: " + msg);
    }
    return 0;
  }),
  loop(sequence([
    transformer((acc: number) => {
      return [acc, ["iter", ["next"]]];
    }),
    smuggle(raise),
    transformer(([acc, msg]: [number, any]) => {
      return [[acc, msg], msg[0] === "some"];
    }),
    if_then_else(
      transformer(([acc, char]: [number, ["some", string]]) => {
        return ["continue", acc * 10 + (char[1].charCodeAt(0) - '0'.charCodeAt(0))];
      }),
      transformer(([acc, char]: [number, ["none"]]) => {
        return ["break", acc];
      }),
    ),
  ]))
]);

describe('ParseInt', () => {
  test('empty string', () => {
    const transcript = new Transcript(parse_int);
    transcript.assertNext(null, 'iter', ['next']);
    transcript.assertNext(['none'], 'result', 0);
  });
  test('non-empty string', () => {
    const transcript = new Transcript(parse_int);
    transcript.assertNext(null, 'iter', ['next']);
    transcript.assertNext(['some', '1'], 'iter', ['next']);
    transcript.assertNext(['some', '2'], 'iter', ['next']);
    transcript.assertNext(['some', '3'], 'iter', ['next']);
    transcript.assertNext(['none'], 'result', 123);
  });
});