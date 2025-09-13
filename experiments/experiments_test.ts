// Test file for experiments.ts
import assert from 'assert';
import { andThen, andThenInit, closure, closure2, closureInit, ClosureState, Combinator, handle, handle2, handleInit, if_then_else, if_then_else2, if_then_else_null, loop, Machine, match, raise, raise2, Result, sequence, sequence2, sequenceInit, smuggle, smuggle2, smuggleInit, Startable, transformer, transformer2, transformerInit } from './experiments';

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

class Transcript2<I, S> {
  machine: Machine<S>;
  state: S;
  constructor(combinator: Combinator<I, S>, state: I) {
    this.machine = combinator.run;
    this.state = combinator.init(state);
  }

  assertNext(input: any, expected_action: string, expected_output: any) {
    const [new_state, result_action, result_output] = handleContinue(this.machine, this.state, input);
    expect([result_action, result_output]).toEqual([expected_action, expected_output]);
    this.state = new_state;
  }
}

function assertTransforms(machine: Machine<any>, input: any): any {
  let result = machine(['start'], input);
  while (result.action === 'continue') {
    result = machine(result.resume_state, result.msg);
  }
  expect(result.action).toEqual('result');
  return result.msg;
}


describe('Transformer', () => {
  const machine = transformer(x => x + 1);
  test('should do the thing', () => {
    const transcript = new Transcript(machine, ['start']);
    transcript.assertNext(2, 'result', 3);
  });
});

function str_iter_init(s: string): ClosureState<StrIterState, ["start"]> {
  return closureInit([s, -1], transformerInit(null));
}

type StrIterState = [string, number];

const str_iter: Machine<ClosureState<StrIterState, ["start"]>> = closure(transformer(([[str, offset], msg]: [StrIterState, ['next' | 'clone']]): [StrIterState, boolean | string] => {
  if (msg[0] === 'next') {
    offset += 1;
    return [[str, offset], offset < str.length];
  }
  if (msg[0] === 'clone') {
    return [[str, offset], str[offset]];
  }
  throw Error('Bad msg: ' + msg[0]);
}));

const str_iter2: Combinator<string, ClosureState<StrIterState, ["start"]>> = {
  init(s: string): ClosureState<StrIterState, ["start"]> {
    return str_iter_init(s);
  },
  run(state: ClosureState<StrIterState, ["start"]>, msg: any): Result<ClosureState<StrIterState, ["start"]>> {
    return str_iter(state, msg);
  }
};

describe('StrIter', () => {
  test('should work with empty string', () => {
    const transcript = new Transcript(str_iter, str_iter_init(''));
    transcript.assertNext(['next'], 'result', false);
  });

  test('should work with non-empty string', () => {
    const transcript = new Transcript(str_iter, str_iter_init('foo'));

    transcript.assertNext(['next'], 'result', true);
    transcript.assertNext(['clone'], 'result', 'f');
    transcript.assertNext(['next'], 'result', true);
    transcript.assertNext(['clone'], 'result', 'o');
    transcript.assertNext(['next'], 'result', true);
    transcript.assertNext(['clone'], 'result', 'o');
    transcript.assertNext(['next'], 'result', false);
  });
});

type StringIterEqualsState = ["start"] | ["await_next", string] | ["await_clone", string] | ["end"];

function string_iter_equals_init(_: null): StringIterEqualsState {
  return ["start"];
}

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

const string_iter_equals2: Combinator<null, StringIterEqualsState> = {
  init(_: null): StringIterEqualsState {
    return string_iter_equals_init(null);
  },
  run(state: StringIterEqualsState, msg: any): Result<StringIterEqualsState> {
    return string_iter_equals(state, msg);
  }
};

describe('StringIterEquals', () => {
  test('should work with empty string', () => {
    const transcript = new Transcript2(string_iter_equals2, null);
    transcript.assertNext('', 'iter', ['next']);
    transcript.assertNext(false, 'result', true);
  });

  test('should work with non-empty string', () => {
    const transcript = new Transcript(string_iter_equals, string_iter_equals_init(null));
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
    const transcript = new Transcript(string_iter_equals, string_iter_equals_init(null));
    transcript.assertNext('foo', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('o', 'iter', ['next']);
    transcript.assertNext(false, 'result', false);
  });

  test('should work with string shorter than iter', () => {
    const transcript = new Transcript(string_iter_equals, string_iter_equals_init(null));
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
    const transcript = new Transcript(string_iter_equals, string_iter_equals_init(null));
    transcript.assertNext('foo', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('r', 'result', false);
  });
});

export type UnclosureState<S> = ["start"] | ["inner", S];

function unclosure2<S>(inner: Combinator<unknown, S>): Combinator<null, UnclosureState<S>> {
  return {
    init(_: null): UnclosureState<S> {
      return ["start"];
    },
    run(state: UnclosureState<S>, msg: any): Result<UnclosureState<S>> {
      if (state[0] === "start") {
        const [state, inner_msg] = msg;
        return { action: "continue", msg: inner_msg, resume_state: ["inner", inner.init(state)] };
      }
      if (state[0] === "inner") {
        const inner_state = state[1];
        const result = inner.run(inner_state, msg);
        return { action: result.action, msg: result.msg, resume_state: ["inner", result.resume_state] };
      }
      throw Error('Bad state: ' + state[0]);
    }
  };
}

const handler = andThen(
  transformer(([action, iter_state, iter_msg]: [string, StrIterState, any]) =>
    [iter_state, iter_msg]),
  str_iter);


// string_iter_equals_inverse := (s) =>
//   let iter := s str_iter_init;
//   let str_iter_equals := null string_iter_equals_init;
//   let bound := handle("iter", iter, str_iter_equals);
//   become(s, bound)
//
//   s => [s, s]
//   smuggle(str_iter_init)
//   [s, iter_state] => [[s, iter_state], null]
//   smuggle(string_iter_equals_init)
//   [[iter_state, s], str_iter_equals_state] => [s, [iter_state, str_iter_equals_state]]
//   smuggle(handleInit)
//   [s, bound] => [s, bound]


// function string_iter_equals_inverse_init(_: null) {
//   return sequenceInit([
//     transformerInit(null), 
//     smuggleInit(transformerInit(null)), 
//     transformerInit(null), 
//     smuggleInit(transformerInit(null)),
//     transformerInit(null),
//     smuggleInit(transformerInit(null)),
//     transformerInit(null),
//     unclosureInit(null),
//   ]);
// }

const string_iter_equals_inverse = sequence2(transformer2((s: string) => [[s, null], s]),
  unclosure2(handle2("iter", str_iter2, string_iter_equals2)),
);

describe('StringIterEqualsInverse', () => {
  test('should work with empty string', () => {
    const transcript = new Transcript2(string_iter_equals_inverse, null);
    transcript.assertNext('', 'result', true);
  });
  test('should work with non-empty string', () => {
    const transcript = new Transcript2(string_iter_equals_inverse, null);
    transcript.assertNext('foo', 'result', true);
  });
});

const char_iter_from_str_iter = sequence2(
  // msg
  transformer2((msg: any) => {
    if (msg[0] !== "next") {
      throw Error("Bad msg: " + msg);
    }
    return ["iter", ["next"]];
  }),
  raise2,
  transformer2((has_next: any) => [null, has_next]),
  if_then_else_null(
    sequence2(
      transformer2((_: any) => ["iter", ["clone"]]),
      raise2,
      transformer2((char: any) => ["some", char]),
    ),
    transformer2((_: any) => ["none"]),
  )
);


describe('CharIterFromStrIter', () => {
  test('unbound with empty string', () => {
    const transcript = new Transcript2(char_iter_from_str_iter, null);
    transcript.assertNext(['next'], 'iter', ['next']);
    transcript.assertNext(false, 'result', ['none']);
  });
  test('unbound with non-empty string', () => {
    const transcript = new Transcript2(char_iter_from_str_iter, null);
    transcript.assertNext(['next'], 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'result', ['some', 'f']);
  });
});

type CharIterFromStringState = [string, number];
const char_iter_from_string_init = transformer2((s: string) => [s, -1]);

const char_iter_from_string = closure2(
  transformer2(([[s, offset], msg]: [CharIterFromStringState, any]) => {
    if (msg[0] !== "next") {
      throw Error("Bad msg: " + msg);
    }
    offset += 1;
    if (offset < s.length) {
      return [[s, offset], ["some", s[offset]]];
    }
    return [[s, offset], ["none"]];
  })
);

describe('CharIterFromString', () => {
  test('empty string', () => {
    const iter = assertTransforms(char_iter_from_string_init.run, '');
    expect(iter).toEqual(['', -1]);

    const transcript = new Transcript2(char_iter_from_string, iter);
    // transcript.assertNext(iter, 'result', null);
    transcript.assertNext(['next'], 'result', ['none']);
  });
  test('non-empty string', () => {
    const iter = assertTransforms(char_iter_from_string_init.run, 'foo');
    expect(iter).toEqual(['foo', -1]);

    const transcript = new Transcript2(char_iter_from_string, iter);
    transcript.assertNext(['next'], 'result', ['some', 'f']);
    transcript.assertNext(['next'], 'result', ['some', 'o']);
    transcript.assertNext(['next'], 'result', ['some', 'o']);
    transcript.assertNext(['next'], 'result', ['none']);
  });
});

// type SSVIterState = ["start"] | ["in_field"] | ["almost_finished"] | ["end"];

// const space_separated_value = sequence([
//   transformer(([state, msg]: [SSVIterState, any]) =>
//     [[state, msg], state[0]]
//   ),
//   match({
//     start:
//       transformer(([state, msg]: [SSVIterState, any]) => {
//         if (msg[0] !== "next") {
//           throw Error("Bad msg: " + msg);
//         }
//         return [["in_field", ["none"]], true];
//       }),
//     in_field: sequence([
//       transformer(([state, msg]: [SSVIterState, any]) => {
//         if (msg[0] !== "inner_next") {
//           throw Error("Bad msg: " + msg);
//         }
//         return ["iter", ["next"]];
//       }),
//       raise,
//       transformer((next_char: ["some", string] | ["none"]) => [next_char, next_char[0] === "some"]),
//       if_then_else(
//         sequence([
//           transformer(([_, char]: ["some", string]) => [char, char === " "]),
//           if_then_else(
//             transformer((_: any) => [["start"], ["none"]]),
//             transformer((char: string) => [["in_field"], ["some", char]]),
//           ),
//         ]),
//         transformer(([_]: ["none"]) => [["almost_finished"], ["none"]]),
//       ),
//     ]),
//     almost_finished:
//       transformer(([state, msg]: [SSVIterState, any]) => {
//         if (msg[0] !== "next") {
//           throw Error("Bad msg: " + msg);
//         }
//         return [["end"], false];
//       }),
//   }),
// ]);

// const space_separated_value_for_string_init = sequence([
//   char_iter_from_string_init,
//   transformer((iter_state: CharIterFromStringState) => [iter_state, ["start"]]),
// ]);

// const space_separated_value_for_string = sequence([
//   transformer(([[char_iter_state, ssv_state], msg]: [[CharIterFromStringState, SSVIterState], any]) =>
//     [char_iter_state, [ssv_state, msg]]),
//   handle("iter", char_iter_from_string, space_separated_value),
//   transformer(([char_iter_state, [ssv_state, msg]]: [CharIterFromStringState, [SSVIterState, any]]) =>
//     [[char_iter_state, ssv_state], msg]),
// ]);

// describe('SpaceSeparatedValue', () => {
//   const closed = closure(space_separated_value_for_string);
//   test('empty string', () => {
//     const transcript = new Transcript(closed);
//     transcript.assertNext(
//       assertTransforms(space_separated_value_for_string_init, ""),
//       'result', null);
//     transcript.assertNext(['next'], 'result', true);
//     transcript.assertNext(['inner_next'], 'result', ['none']);
//     transcript.assertNext(['next'], 'result', false);
//   });
//   test('one field', () => {
//     const transcript = new Transcript(closed);
//     transcript.assertNext(
//       assertTransforms(space_separated_value_for_string_init, "foo"),
//       'result', null);
//     transcript.assertNext(['next'], 'result', true);
//     transcript.assertNext(['inner_next'], 'result', ['some', 'f']);
//     transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
//     transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
//     transcript.assertNext(['inner_next'], 'result', ['none']);
//     transcript.assertNext(['next'], 'result', false);
//   });

//   test('double field', () => {
//     const transcript = new Transcript(closed);
//     transcript.assertNext(
//       assertTransforms(space_separated_value_for_string_init, "foo b"),
//       'result', null);
//     transcript.assertNext(['next'], 'result', true);
//     transcript.assertNext(['inner_next'], 'result', ['some', 'f']);
//     transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
//     transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
//     transcript.assertNext(['inner_next'], 'result', ['none']);
//     transcript.assertNext(['next'], 'result', true);
//     transcript.assertNext(['inner_next'], 'result', ['some', 'b']);
//     transcript.assertNext(['inner_next'], 'result', ['none']);
//     transcript.assertNext(['next'], 'result', false);
//   });
// });

// const parse_int = sequence([
//   transformer((msg: null) => {
//     if (msg !== null) {
//       throw Error("Bad msg: " + msg);
//     }
//     return 0;
//   }),
//   loop(sequence([
//     transformer((acc: number) => {
//       return [acc, ["iter", ["next"]]];
//     }),
//     smuggle(raise),
//     transformer(([acc, msg]: [number, any]) => {
//       return [[acc, msg], msg[0] === "some"];
//     }),
//     if_then_else(
//       transformer(([acc, char]: [number, ["some", string]]) => {
//         return ["continue", acc * 10 + (char[1].charCodeAt(0) - '0'.charCodeAt(0))];
//       }),
//       transformer(([acc, char]: [number, ["none"]]) => {
//         return ["break", acc];
//       }),
//     ),
//   ]))
// ]);

// describe('ParseInt', () => {
//   test('empty string', () => {
//     const transcript = new Transcript(parse_int);
//     transcript.assertNext(null, 'iter', ['next']);
//     transcript.assertNext(['none'], 'result', 0);
//   });
//   test('non-empty string', () => {
//     const transcript = new Transcript(parse_int);
//     transcript.assertNext(null, 'iter', ['next']);
//     transcript.assertNext(['some', '1'], 'iter', ['next']);
//     transcript.assertNext(['some', '2'], 'iter', ['next']);
//     transcript.assertNext(['some', '3'], 'iter', ['next']);
//     transcript.assertNext(['none'], 'result', 123);
//   });
// });

// const parse_int_from_string = sequence([
//   char_iter_from_string_init,
//   transformer((iter_state: CharIterFromStringState) => [iter_state, null]),
//   handle("iter", char_iter_from_string, parse_int),
//   transformer(([iter_state, result]: [CharIterFromStringState, number]) => result),
// ]);

// describe('ParseIntFromString', () => {
//   test('empty string', () => {
//     const transcript = new Transcript(parse_int_from_string);
//     transcript.assertNext("", 'result', 0);
//   });
//   test('non-empty string', () => {
//     const transcript = new Transcript(parse_int_from_string);
//     transcript.assertNext("1234", 'result', 1234);
//   });
// });