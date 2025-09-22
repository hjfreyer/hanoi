// Test file for experiments.ts
import { fchownSync } from 'fs';
import { andThen, closure, ClosureState, Combinator, handle, if_then_else_null, loop, Machine, match, raise, Result, sequence, SequenceState, smuggle, t, construct, withInit, func, FuncState, call, ret, curryState } from './experiments';

function handleContinue<S>(machine: Machine<S>, state: S, input: any): [S, string, any] {
  console.log("handleContinue", state, input);
  let result = machine(state, input);
  while (result.action === 'continue') {
    state = result.resume_state;
  console.log("handleContinue", state, result.msg);

    result = machine(state, result.msg);
  }
  return [result.resume_state, result.action, result.msg];
}

class Transcript<I, S> {
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


class FuncTranscript<S> {
  machine: Machine<FuncState<S>>;
  state: FuncState<S>;
  constructor(machine: Machine<FuncState<S>>) {
    this.machine = machine;
    this.state = ["start"];
  }

  assertNext(input: any, expected_action: string, expected_output: any) {
    const [new_state, result_action, result_output] = handleContinue(this.machine, this.state, input);
    expect([result_action, result_output]).toEqual([expected_action, expected_output]);
    this.state = new_state;
  }
}

function assertTransforms(machine: Combinator<null, unknown>, input: any): any {
  let result = machine.run(machine.init(null), input);
  while (result.action === 'continue') {
    result = machine.run(result.resume_state, result.msg);
  }
  expect(result.action).toEqual('result');
  return result.msg;
}

describe('Transformer', () => {
  const machine = t(x => x + 1);
  test('should do the thing', () => {
    const transcript = new Transcript(machine, null);
    transcript.assertNext(2, 'result', 3);
  });
});

const str_iter_init: Combinator<null, ["start"]> = t((s: string) => [s, -1]);

type StrIterState = [string, number];

const str_iter2: Combinator<StrIterState, ClosureState<StrIterState, ["start"]>> = closure(t(([[str, offset], msg]: [StrIterState, ['next' | 'clone']]): [StrIterState, boolean | string] => {
  if (msg[0] === 'next') {
    offset += 1;
    return [[str, offset], offset < str.length];
  }
  if (msg[0] === 'clone') {
    return [[str, offset], str[offset]];
  }
  throw Error('Bad msg: ' + msg[0]);
}));


describe('StrIter', () => {
  test('should work with empty string', () => {
    const transcript = new Transcript(str_iter2, ['', -1]);
    transcript.assertNext(['next'], 'result', false);
  });

  test('should work with non-empty string', () => {
    const transcript = new Transcript(str_iter2, ['foo', -1]);

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
    const transcript = new Transcript(string_iter_equals2, null);
    transcript.assertNext('', 'iter', ['next']);
    transcript.assertNext(false, 'result', true);
  });

  test('should work with non-empty string', () => {
    const transcript = new Transcript(string_iter_equals2, null);
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
    const transcript = new Transcript(string_iter_equals2, null);
    transcript.assertNext('foo', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('o', 'iter', ['next']);
    transcript.assertNext(false, 'result', false);
  });

  test('should work with string shorter than iter', () => {
    const transcript = new Transcript(string_iter_equals2, null);
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
    const transcript = new Transcript(string_iter_equals2, null);
    transcript.assertNext('foo', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('r', 'result', false);
  });
});

const string_iter_equals_inverse = sequence(
  t((s: string) => [s, s]),
  smuggle(str_iter_init),
  t(([s, str_iter]) => [[str_iter, null], s]),
  construct(handle("iter", str_iter2, string_iter_equals2)),
);

describe('StringIterEqualsInverse', () => {
  test('should work with empty string', () => {
    const transcript = new Transcript(string_iter_equals_inverse, null);
    transcript.assertNext('', 'result', true);
  });
  test('should work with non-empty string', () => {
    const transcript = new Transcript(string_iter_equals_inverse, null);
    transcript.assertNext('foo', 'result', true);
  });
});

const char_iter_from_str_iter = func(sequence(
  // msg
  t((msg: any) => {
    if (msg[0] !== "next") {
      throw Error("Bad msg: " + msg);
    }
    return ["iter", ["next"]];
  }),
  raise,
  t((has_next: any) => [null, has_next]),
  if_then_else_null(
    sequence(
      t((_: any) => ["iter", ["clone"]]),
      raise,
      t((char: any) => ["some", char]),
    ),
    t((_: any) => ["none"]),
  )
));


describe('CharIterFromStrIter', () => {
  test('unbound with empty string', () => {
    const transcript = new FuncTranscript(char_iter_from_str_iter);
    transcript.assertNext(['next'], 'iter', ['next']);
    transcript.assertNext(false, 'result', ['none']);
  });
  test('unbound with non-empty string', () => {
    const transcript = new FuncTranscript(char_iter_from_str_iter);
    transcript.assertNext(['next'], 'iter', ['next']);
    transcript.assertNext(true, 'iter', ['clone']);
    transcript.assertNext('f', 'result', ['some', 'f']);
  });
});

type CharIterFromStringState = [string, number];
const char_iter_from_string_init = func(t((s: string) => [s, -1]));

const char_iter_from_string = func(
  t(([[s, offset], msg]: [CharIterFromStringState, any]) => {
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

const nullhandler = t(msg => { throw Error("Bad msg: " + msg) });

// const char_iter_from_string_closure = func(sequence(
//   t((msg: any) => [msg, ["input", ["clone"]]]),
//   smuggle(raise),
//   call(char_iter_from_string_init, nullhandler),
//   t(([msg, iter_state]: [any, CharIterFromStringState]) => [iter_state, msg]),
//   loop( // [iter_state, msg]
//     sequence(
//       t(([iter_state, msg]: [CharIterFromStringState, any]) => [null, [iter_state, msg]]),
//       call(char_iter_from_string, nullhandler),
//       t(([_, [iter_state, msg]]: [any, [CharIterFromStringState, any]]) => [iter_state, msg]),
//       smuggle(ret),
//       t(([iter_state, msg]: [CharIterFromStringState, any]) => ["continue", [iter_state, msg]]),
//     )
//   )
// ));

const char_iter_from_string_closure = curryState(char_iter_from_string_init, char_iter_from_string);
  
//   func(sequence(
//   t((msg: any) => [msg, ["input", ["clone"]]]),
//   smuggle(raise),
//   call(char_iter_from_string_init, nullhandler),
//   t(([msg, iter_state]: [any, CharIterFromStringState]) => [iter_state, msg]),
//   loop( // [iter_state, msg]
//     sequence(
//       t(([iter_state, msg]: [CharIterFromStringState, any]) => [null, [iter_state, msg]]),
//       call(char_iter_from_string, nullhandler),
//       t(([_, [iter_state, msg]]: [any, [CharIterFromStringState, any]]) => [iter_state, msg]),
//       smuggle(ret),
//       t(([iter_state, msg]: [CharIterFromStringState, any]) => ["continue", [iter_state, msg]]),
//     )
//   )
// ));

describe('CharIterFromString', () => {
  test('empty string', () => {
    // const iter = assertTransforms(char_iter_from_string_init, '');
    // expect(iter).toEqual(['', -1]);

    const transcript = new FuncTranscript(char_iter_from_string_closure);
    transcript.assertNext(['next'], 'input', ['clone']);
    transcript.assertNext('', 'result', ['none']);
  });
  test('non-empty string', () => {
    // const iter = assertTransforms(char_iter_from_string_init, 'foo');
    // expect(iter).toEqual(['foo', -1]);

    const transcript = new FuncTranscript(char_iter_from_string_closure);
    transcript.assertNext(['next'], 'input', ['clone']);
    transcript.assertNext('foo', 'result', ['some', 'f']);
    transcript.assertNext(['next'], 'result', ['some', 'o']);
    transcript.assertNext(['next'], 'result', ['some', 'o']);
    transcript.assertNext(['next'], 'result', ['none']);
  });
});

type SSVIterState = ["start"] | ["in_field"] | ["almost_finished"] | ["end"];

const space_separated_value = func(withInit(["start"], closure(sequence(
  t(([state, msg]: [SSVIterState, any]) =>
    [[state, msg], state[0]]
  ),
  match({
    start:
      t(([state, msg]: [SSVIterState, any]) => {
        if (msg[0] !== "next") {
          throw Error("Bad msg: " + msg);
        }
        return [["in_field", ["none"]], true];
      }),
    in_field: sequence(
      t(([state, msg]: [SSVIterState, any]) => {
        if (msg[0] !== "inner_next") {
          throw Error("Bad msg: " + msg);
        }
        return ["iter", ["next"]];
      }),
      raise,
      t((next_char: ["some", string] | ["none"]) => [next_char, next_char[0] === "some"]),
      if_then_else_null(
        sequence(
          t(([_, char]: ["some", string]) => [char, char === " "]),
          if_then_else_null(
            t((_: any) => [["start"], ["none"]]),
            t((char: string) => [["in_field"], ["some", char]]),
          ),
        ),
        t(([_]: ["none"]) => [["almost_finished"], ["none"]]),
      ),
    ),
    almost_finished:
      t(([state, msg]: [SSVIterState, any]) => {
        if (msg[0] !== "next") {
          throw Error("Bad msg: " + msg);
        }
        return [["end"], false];
      }),
  }),
))));

const space_separated_value_for_string_init = func(sequence(
  t((s: string) => [null, s]),
  call(char_iter_from_string_init, nullhandler),
  t(([_, iter_state]: [null, CharIterFromStringState]) => [iter_state, null]),
));


const space_separated_value_for_string = func(
  sequence(
    t((msg: any) => [msg, ["input", ["clone"]]]),
    call(char_iter_from_string_init, nullhandler),
    t(([msg, iter_state]: [any, CharIterFromStringState]) => [iter_state, msg]),
    smuggle(ret),
    t(([iter_state, msg]: [CharIterFromStringState, any]) => ["continue", [iter_state, msg]]),
  )
);

const space_separated_value_for_string_closure = curryState(space_separated_value_for_string_init, space_separated_value_for_string);

// handle("iter", char_iter_from_string, space_separated_value);

describe('SpaceSeparatedValue', () => {
  // const closed = closure(space_separated_value_for_string);
  test('empty string', () => {
    // const init = assertTransforms(space_separated_value_for_string_init, "");

    const transcript = new FuncTranscript(space_separated_value_for_string_closure);
    transcript.assertNext(['next'], 'input', ['clone']);
    transcript.assertNext('', 'result', true);
    
    transcript.assertNext(['inner_next'], 'result', ['none']);
    transcript.assertNext(['next'], 'result', false);
  });
  // test('one field', () => {
  //   const init = assertTransforms(space_separated_value_for_string_init, "foo");

  //   const transcript = new Transcript(space_separated_value_for_string, init);
  //   transcript.assertNext(['next'], 'result', true);
  //   transcript.assertNext(['inner_next'], 'result', ['some', 'f']);
  //   transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
  //   transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
  //   transcript.assertNext(['inner_next'], 'result', ['none']);
  //   transcript.assertNext(['next'], 'result', false);
  // });

  // test('double field', () => {
  //   const init = assertTransforms(space_separated_value_for_string_init, "foo b");
  //   const transcript = new Transcript(space_separated_value_for_string, init);
  //   transcript.assertNext(['next'], 'result', true);
  //   transcript.assertNext(['inner_next'], 'result', ['some', 'f']);
  //   transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
  //   transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
  //   transcript.assertNext(['inner_next'], 'result', ['none']);
  //   transcript.assertNext(['next'], 'result', true);
  //   transcript.assertNext(['inner_next'], 'result', ['some', 'b']);
  //   transcript.assertNext(['inner_next'], 'result', ['none']);
  //   transcript.assertNext(['next'], 'result', false);
  // });
});

// const parse_int = func(sequence(
//   t((msg: null) => {
//     if (msg !== null) {
//       throw Error("Bad msg: " + msg);
//     }
//     return 0;
//   }),
//   loop(sequence(
//     t((acc: number) => {
//       return [acc, ["iter", ["next"]]];
//     }),
//     smuggle(raise),
//     t(([acc, msg]: [number, any]) => {
//       return [[acc, msg], msg[0] === "some"];
//     }),
//     if_then_else_null(
//       t(([acc, char]: [number, ["some", string]]) => {
//         return ["continue", acc * 10 + (char[1].charCodeAt(0) - '0'.charCodeAt(0))];
//       }),
//       t(([acc, char]: [number, ["none"]]) => {
//         return ["break", acc];
//       }),
//     ),
//   ))
// ));

// describe('ParseInt', () => {
//   test('empty string', () => {
//     const transcript = new Transcript(parse_int, null);
//     transcript.assertNext(null, 'iter', ['next']);
//     transcript.assertNext(['none'], 'result', 0);
//   });
//   test('non-empty string', () => {
//     const transcript = new Transcript(parse_int, null);
//     transcript.assertNext(null, 'iter', ['next']);
//     transcript.assertNext(['some', '1'], 'iter', ['next']);
//     transcript.assertNext(['some', '2'], 'iter', ['next']);
//     transcript.assertNext(['some', '3'], 'iter', ['next']);
//     transcript.assertNext(['none'], 'result', 123);
//   });
// });

// const parse_int_from_string = sequence(
//   char_iter_from_string_init,
//   t((iter_state: CharIterFromStringState) => [[iter_state, null], null]),
//   construct(handle("iter", char_iter_from_string, parse_int)),
// );

// describe('ParseIntFromString', () => {
//   test('empty string', () => {
//     const transcript = new Transcript(parse_int_from_string, null);
//     transcript.assertNext("", 'result', 0);
//   });
//   test('non-empty string', () => {
//     const transcript = new Transcript(parse_int_from_string, null);
//     transcript.assertNext("1234", 'result', 1234);
//   });
// });

// type IterMapState = ["start" | "middle" | "end"];

// const iter_map = func(withInit(["start"], closure(sequence(
//   t(([state, msg]: [IterMapState, any]) => [[state, msg], msg[0]]),
//   match({
//     next: sequence(
//       t(([state, msg]: [IterMapState, any]) => null),
//       sequence(
//         t((_: null) => ["iter", ["next"]]),
//         raise,
//         t((has_next: boolean) => {
//           if (has_next) {
//             return [["middle"], true];
//           } else {
//             return [["end"], false];
//           }
//         }),
//       ),
//     ),
//     item: sequence(
//       t(([state, msg]: [IterMapState, any]) => {
//         if (state[0] !== "middle") {
//           throw Error("Bad state: " + state[0]);
//         }
//         return msg[1];
//       }),
//       loop(sequence(
//         t((msg: any) => ["fn", msg]),
//         raise,
//         t(([action, msg]: any) => [msg, action]),
//         match({
//           input: sequence(
//             t((msg: any) => ["iter", ["item", msg]]),
//             raise,
//             t((resp: any) => ["continue", resp]),
//           ),
//           result: t((resp: any) => {
//             return ["break", ["middle", resp]];
//           }),
//         }),
//       )),
//     ),
//   }),
// ))));

// const doubler = func(sequence(
//   t((msg: any) => {
//     if (msg[0] !== "clone") {
//       throw Error("Bad msg: " + msg);
//     }
//     return ["input", ["clone"]];
//   }),
//   raise,
//   t((msg: number) => {
//     return msg * 2;
//   }),
// ));

// describe('IterMap', () => {
//   test('empty iter', () => {
//     const transcript = new Transcript(iter_map, null);
//     transcript.assertNext(['next'], 'iter', ['next']);
//     transcript.assertNext(false, 'result', false);
//   });
//   test('double ints', () => {
//     const transcript = new Transcript(iter_map, null);
//     transcript.assertNext(['next'], 'iter', ['next']);
//     transcript.assertNext(true, 'result', true);
//     transcript.assertNext(['item', ['clone']], 'fn', ['clone']);
//     transcript.assertNext(['input', ['clone']], 'iter', ['item', ['clone']]);
//     transcript.assertNext(3, 'fn', 3);
//     transcript.assertNext(['result', 6], 'result', 6);
//     transcript.assertNext(['next'], 'iter', ['next']);
//     transcript.assertNext(false, 'result', false);
//   });
//   test('doubler', () => {
//     const transcript = new Transcript(doubler, null);
//     transcript.assertNext(['clone'], 'input', ['clone']);
//     transcript.assertNext(3, 'result', 6);
//   });
// });
