// Test file for experiments.ts
// import { Machine, t, FuncFragment, func, Function, closure, Action } from './experiments';

import { assert } from "console";

type Machine = {
  kind: "fn",
  fn: (arg: any) => any
} | {
  kind: "stateful",
  state: any,
  fn: (state: any, arg: any) => [any, any]
} | {
  kind: "bind",
  machine: Machine,
  handler: Machine,
} | {
  kind: "cond",
  true_branch: Machine,
  false_branch: Machine,
} | {
  kind: "match",
  cases: { [key: string]: Machine },
} | {
  kind: "latch",
  cases: { [key: string]: Machine },
} | {
  kind: "sequence",
  machines: Machine[]
} | {
  kind: "loop",
  body: Machine,
} | {
  kind: "yield",
  // handler: Machine,
}

function machine_apply(machine: Machine, state: any, input: any): [any, any] {
  if (machine.kind === "fn") {
    return [null, machine.fn(input)];
  } else if (machine.kind === "stateful") {
    const [new_state, result] = machine.fn(machine.state, input);
    return [new_state, result];
    // } else if (machine.kind === "cond") {
    //   const [carry, cond] = input;
    //   if (cond === true) {
    //     return machine_apply(machine.true_branch, carry);
    //   } else if (cond === false) {
    //     return machine_apply(machine.false_branch, carry);
    //   } else {
    //     throw Error("Bad cond: " + JSON.stringify(cond));
    //   }
    // } else if (machine.kind === "match") {
    //   const case_fn = machine.cases[input.kind];
    //   if (case_fn === undefined) {
    //     throw Error("Bad match: " + JSON.stringify(input.kind));
    //   }
    //   const [new_machine, result] = machine_apply(case_fn, input.inner);
    //   return [{ kind: "match", cases: { ...machine.cases, [input.kind]: new_machine } }, result];
  } else if (machine.kind === "latch") {
    if (state.kind === "start") {
      const [ctx, tag] = input
      return machine_apply(machine, { kind: "latch", tag, inner: { kind: "start" } }, ctx);
    } else if (state.kind === "latch") {
      const case_fn = machine.cases[state.tag];
      if (case_fn === undefined) {
        throw Error("Bad latch: " + JSON.stringify(state.tag));
      }
      const [new_state, result] = machine_apply(case_fn, state.inner, input);
      return [{ kind: "latch", tag: state.tag, inner: new_state }, result];
    } else {
      throw Error("Bad latch state: " + JSON.stringify(state));
    }
  } else if (machine.kind === "sequence") {
    if (state.kind === "start") {
      return machine_apply(machine, { kind: "step", index: 0, inner: { kind: "start" } }, input);
    } else if (state.kind === "step") {
      const [new_state, result] = machine_apply(machine.machines[state.index], state.inner, input);
      if (state.index === machine.machines.length - 1) {
        return [{ kind: "step", index: state.index, inner: new_state }, result];
      } else if (result.kind === "break") {
        return [{ kind: "step", index: state.index, inner: new_state }, result.inner];
      } else if (result.kind === "result") {
        return machine_apply(machine, { kind: "step", index: state.index + 1, inner: { kind: "start" } }, result.inner);
      } else {
        throw Error("Bad sequence result: " + JSON.stringify(result));
      }
    } else {
      throw Error("Bad sequence state: " + JSON.stringify(state));
    }
  } else if (machine.kind === "loop") {
    const [new_state, result] = machine_apply(machine.body, state, input);
    if (result.kind === "break") {
      return [new_state, result.inner];
    } else if (result.kind === "continue") {
      return machine_apply(machine, { kind: "start" }, result.inner);
    } else {
      throw Error("Bad loop result: " + JSON.stringify(result));
    }
  } else if (machine.kind === "yield") {
    if (state.kind === "start") {
      const [ctx, inner] = input;
      return [{ kind: "waiting", ctx }, inner];
    } else if (state.kind === "waiting") {
      return [{ kind: "done" }, { kind: "result", inner: [state.ctx, input] }];
    } else {
      throw Error("Bad yield state: " + JSON.stringify(state));
    }
  } else {
    throw Error("Bad machine: " + JSON.stringify(machine));
  }
}

function t(f: (...args: any[]) => any): Machine {
  return {
    kind: "fn",
    fn: f,
  }
}

function sequence(...machines: Machine[]): Machine {
  return {
    kind: "sequence",
    machines: machines,
  }
}

function loop(body: Machine): Machine {
  return {
    kind: "loop",
    body: body,
  }
}

function brk(inner: any) {
  return {
    kind: "break",
    inner: inner,
  }
}

function res(inner: any) {
  return {
    kind: "result",
    inner: inner,
  }
}

function cont(inner: any) {
  return {
    kind: "continue",
    inner: inner,
  }
}

function latch(cases: { [key: string]: Machine }): Machine {
  return {
    kind: "latch",
    cases: cases,
  }
}

const argmin_between_machine: Machine = sequence(
  t(([start, end]: [number, number]) => { return { kind: "result", inner: [start, end, start] } }),
  loop(
    sequence(
      t(([start, end, argmin]: [number, number, number]) => {
        if (start === end) {
          return brk(brk(res(argmin)));
        }
        return res([[start, end, argmin], null]);
      }),
      loop(
        sequence(
          t(([ctx, msg]) => res([ctx, brk(brk(brk(brk({ kind: "cmp", inner: msg }))))])),
          { kind: "yield" },
          t(([ctx, action]) => res([[ctx, action], action.kind])),
          latch({
            result: t(([ctx, action]) => brk(res([ctx, action.inner]))),
            send_a: sequence(
              t(([[start, end, argmin], action]) => res([[start, end, argmin], { kind: "item", index: start, inner: action.inner }])),
              loop(sequence(
                t(([ctx, list_arg]) =>
                  res([ctx, brk(brk(brk(brk(brk({ kind: "list", inner: list_arg })))))]),
                ),
                { kind: "yield" },
                t(([ctx, action]) => res([[ctx, action], action.kind])),
                latch({
                  result: t(([ctx, action]) => brk(cont([ctx, action.inner]))),
                })
              ))),
            send_b: sequence(
              t(([[start, end, argmin], action]) => res([[start, end, argmin], { kind: "item", index: argmin, inner: action.inner }])),
              loop(sequence(
                t(([ctx, list_arg]) =>
                  res([ctx, brk(brk(brk(brk(brk({ kind: "list", inner: list_arg })))))]),
                ),
                { kind: "yield" },
                t(([ctx, action]) => res([[ctx, action], action.kind])),
                latch({
                  result: t(([ctx, action]) => brk(cont([ctx, action.inner]))),
                })
              ))),
          }),
        )
      ),
      t(([[start, end, argmin], ord]) => {
        if (ord === '<') {
          return cont([start + 1, end, start]);
        } else if (ord === '>' || ord === '=') {
          return cont([start + 1, end, argmin]);
        } else {
          throw Error("Bad ord: " + ord);
        }
      })
    )
  )
);

describe("argmin_between", () => {
  test("should work", () => {
    let [state, result] = machine_apply(argmin_between_machine, { kind: "start" }, [0, 3]);
    expect(result).toEqual({ kind: "cmp", inner: null });
    [state, result] = machine_apply(argmin_between_machine, state, { kind: "send_a", inner: "senda" });
    expect(result).toEqual({ kind: "list", inner: { kind: "item", index: 0, inner: "senda" } });
    [state, result] = machine_apply(argmin_between_machine, state, res("returna"));
    expect(result).toEqual({ kind: "cmp", inner: "returna" });
    [state, result] = machine_apply(argmin_between_machine, state, { kind: "send_b", inner: "sendb" });
    expect(result).toEqual({ kind: "list", inner: { kind: "item", index: 0, inner: "sendb" } });
    [state, result] = machine_apply(argmin_between_machine, state, res("returnb"));
    expect(result).toEqual({ kind: "cmp", inner: "returnb" });
    [state, result] = machine_apply(argmin_between_machine, state, res("<"));
    expect(result).toEqual({ kind: "cmp", inner: null });
    [state, result] = machine_apply(argmin_between_machine, state, { kind: "send_a", inner: "senda" });
    expect(result).toEqual({ kind: "list", inner: { kind: "item", index: 1, inner: "senda" } });
    [state, result] = machine_apply(argmin_between_machine, state, res("returna"));
    expect(result).toEqual({ kind: "cmp", inner: "returna" });
    [state, result] = machine_apply(argmin_between_machine, state, { kind: "send_b", inner: "sendb" });
    expect(result).toEqual({ kind: "list", inner: { kind: "item", index: 0, inner: "sendb" } });
    [state, result] = machine_apply(argmin_between_machine, state, res("returnb"));
    expect(result).toEqual({ kind: "cmp", inner: "returnb" });
    [state, result] = machine_apply(argmin_between_machine, state, res("<"));
    expect(result).toEqual({ kind: "cmp", inner: null });
    [state, result] = machine_apply(argmin_between_machine, state, res("="));
    expect(result).toEqual(res(1));
  });
});

const builtin_cmp_machine: Machine = sequence(
  t((_) => res([null, brk({ kind: "send_a", inner: { kind: "get" } })])),
  { kind: "yield" },
  t(([ctx, msg]) => {
    assert(msg.kind === "result");
    return res([msg.inner, brk({ kind: "send_b", inner: { kind: "get" } })]);
  }),
  { kind: "yield" },
  t(([a_val, b_val_result]) => {
    assert(b_val_result.kind === "result");
    const b_val = b_val_result.inner;
    let ord;
    if (a_val < b_val) {
      ord = '<';
    } else if (a_val > b_val) {
      ord = '>';
    } else {
      ord = '=';
    }
    return res([[ord, b_val], brk({ kind: "send_a", inner: { kind: "set", inner: a_val } })]);
  }),
  { kind: "yield" },
  t(([[ord, b_val], msg]) => {
    return res([ord, brk({ kind: "send_b", inner: { kind: "set", inner: b_val } })]);
  }),
  { kind: "yield" },
  t(([ord, msg]) => {
    return brk(res(ord));
  }),
);

describe("builtin_cmp", () => {
  test("should work", () => {
    let [state, result] = machine_apply(builtin_cmp_machine, { kind: "start" }, null);
    expect(result).toEqual({ kind: "send_a", inner: { kind: "get" } });
    [state, result] = machine_apply(builtin_cmp_machine, state, res(3));
    expect(result).toEqual({ kind: "send_b", inner: { kind: "get" } });
    [state, result] = machine_apply(builtin_cmp_machine, state, res(2));
    expect(result).toEqual({ kind: "send_a", inner: { kind: "set", inner: 3 } });
    [state, result] = machine_apply(builtin_cmp_machine, state, res(null));
    expect(result).toEqual({ kind: "send_b", inner: { kind: "set", inner: 2 } });
    [state, result] = machine_apply(builtin_cmp_machine, state, res(null));
    expect(result).toEqual(res('>'));
  });
});

function* argmin_between_g(min, max): Generator<any, [any, number], any> {
  if (min === max) {
    return min;
  } else {
    const rec_argmin = yield* argmin_between_g(min + 1, max);
    let [_, min_result] = yield* yield_and_stateful_bind("cmp", [], { min, rec_argmin }, {
      *send_a({ min, rec_argmin }, msg) {
        return [{ min, rec_argmin }, yield {
          kind: "request", fn: "list", args: [{
            kind: "request", fn: "item", args: [min, msg]
          }]
        }];
      },
      *send_b({ min, rec_argmin }, msg) {
        return [{ min, rec_argmin }, yield {
          kind: "request", fn: "list", args: [{
            kind: "request", fn: "item", args: [rec_argmin, msg]
          }]
        }];
      }
    });

    if (min_result === '<') {
      return min;
    } else if (min_result === ">" || min_result === "=") {
      return rec_argmin;
    } else {
      throw Error("bad min_result: " + min_result)
    }
  }
}


describe("min_between", () => {
  test("should work with bound", () => {
    const list = [3, 1, 2];
    const bound = stateful_bind(argmin_between_g(0, 2), list, {
      *cmp(list, msg) {
        return [list, yield* builtin_cmp_g_impl(msg)];
      },
      list: value_list_impl,
    });
    expect(bound.next().value[1]).toEqual(1);
  });
});

function* sort_list_helper(start, end): Generator<any, any, any> {
  if (start === end) {
    return null;
  }
  const min = yield* argmin_between_g(start, end);
  yield { kind: "request", fn: "list", args: [{ kind: "request", fn: "swap", args: [min, start] }] };
  return yield* sort_list_helper(start + 1, end);
}

function* sort_list(): Generator<any, null, any> {
  const len = yield { kind: "request", fn: "list", args: [{ kind: "request", fn: "len", args: [] }] };
  return yield* sort_list_helper(0, len - 1);
}

function* list_impl<T>(list: T[], msg: any): Generator<any, [T[], any], any> {
  assert(msg.kind === "request");
  if (msg.fn === "len") {
    return [list, list.length];
  } else if (msg.fn === "swap") {
    const [index1, index2] = msg.args;
    const tmp = list[index1];
    list[index1] = list[index2];
    list[index2] = tmp;
    return [list, null];
  } else if (msg.fn === "new_iter") {
    return [list, { index: -1, len: list.length }];
  } else if (msg.fn === "iter_next") {
    const [iter] = msg.args;
    return [list, yield* list_iter_next(iter)];
  } else if (msg.fn === "iter_item") {
    const [iter, inner_msg] = msg.args;
    const item = list[iter.index];
    const [new_item, result] = yield { kind: "request", fn: "item", args: [item, inner_msg] };
    list[iter.index] = new_item;
    return [list, [iter, result]];
  } else if (msg.fn === "item") {
    const [index, inner_msg] = msg.args;
    const item = list[index];
    const [new_item, result] = yield { kind: "request", fn: "item", args: [item, inner_msg] };
    list[index] = new_item;
    return [list, result];
  } else {
    throw Error("Bad request: " + JSON.stringify(msg));
  }
}

function* value_list_impl<T>(list: T[], msg: any): Generator<any, [T[], any], any> {
  assert(msg.kind === "request");
  if (msg.fn === "len") {
    return [list, list.length];
  } else if (msg.fn === "swap") {
    const [index1, index2] = msg.args;
    const tmp = list[index1];
    list[index1] = list[index2];
    list[index2] = tmp;
    return [list, null];
  } else if (msg.fn === "new_iter") {
    return [list, { index: -1, len: list.length }];
  } else if (msg.fn === "iter_next") {
    const [iter] = msg.args;
    return [list, yield* list_iter_next(iter)];
  } else if (msg.fn === "iter_item") {
    const [iter, inner_msg] = msg.args;
    assert(inner_msg.kind === "request");
    if (inner_msg.fn === "get") {
      return [list, [iter, list[iter.index]]];
    } else if (inner_msg.fn === "set") {
      list[iter.index] = inner_msg.args[0];
      return [list, [iter, null]];
    } else {
      throw Error("Bad request: " + JSON.stringify(inner_msg));
    }
  } else if (msg.fn === "item") {
    const [index, inner_msg] = msg.args;
    assert(inner_msg.kind === "request");
    if (inner_msg.fn === "get") {
      return [list, list[index]];
    } else if (inner_msg.fn === "set") {
      list[index] = inner_msg.args[0];
      return [list, null];
    } else {
      throw Error("Bad request: " + JSON.stringify(inner_msg));
    }
  } else {
    throw Error("Bad request: " + JSON.stringify(msg));
  }
}

function* string_impl(str: string, msg: any): Generator<any, [string, any], any> {
  assert(msg.kind === "request");
  if (msg.fn === "len") {
    return [str, str.length];
  } else if (msg.fn === "new_iter") {
    return [str, { index: -1, len: str.length }];
  } else if (msg.fn === "iter_next") {
    const [iter] = msg.args;
    const index = iter.index + 1;
    if (index === iter.len) {
      return [str, [{ index: index, len: iter.len }, false]];
    } else {
      return [str, [{ index: index, len: iter.len }, true]];
    }
  } else if (msg.fn === "iter_item") {
    const [iter, inner_msg] = msg.args;
    assert(inner_msg.kind === "request");
    if (inner_msg.fn === "get") {
      return [str, [iter, str[iter.index]]];
    } else {
      throw Error("Bad request: " + JSON.stringify(msg));
    }
  } else {
    throw Error("Bad request: " + JSON.stringify(msg));
  }
}

function* string_cmp() {
  const iter_a = yield { kind: "request", fn: "send_a", args: [{ kind: "request", fn: "new_iter", args: [] }] };
  const iter_b = yield { kind: "request", fn: "send_b", args: [{ kind: "request", fn: "new_iter", args: [] }] };
  const [spent_iters, result] = yield* stateful_bind(iterator_cmp(), { iter_a, iter_b }, {

  });
}

function* name_impl({ first, last }, msg) {
  if (msg.kind === "send_first") {
    const [new_first, result] = yield* string_impl(first, msg);
    return [{ first: new_first, last }, result];
  } else if (msg.kind === "send_last") {
    const [new_last, result] = yield* string_impl(last, msg);
    return [{ first, last: new_last }, result];
  } else {
    throw Error("Bad message: " + JSON.stringify(msg));
  }
}

// function* name_cmp() {
//   const first_cmp = yield { kind: "request", fn: "send_a", args: [{ kind: "send_" }] };
// }

function* builtin_cmp(a_val, b_val): any {
  if (a_val < b_val) {
    return [a_val, b_val, '<'];
  } else if (a_val > b_val) {
    return [a_val, b_val, '>'];
  } else {
    return [a_val, b_val, '='];
  }
}

function* builtin_cmp_g() {
  let a_val = yield { kind: "request", fn: "send_a", args: [{ kind: "request", fn: "get", args: [] }] };
  let b_val = yield { kind: "request", fn: "send_b", args: [{ kind: "request", fn: "get", args: [] }] };
  const [new_a_val, new_b_val, result] = yield* builtin_cmp(a_val, b_val);
  yield { kind: "request", fn: "send_a", args: [{ kind: "request", fn: "set", args: [new_a_val] }] };
  yield { kind: "request", fn: "send_b", args: [{ kind: "request", fn: "set", args: [new_b_val] }] };
  return result;
}

type BuiltinCmpGState = { gen: Generator<any, any, any> };
type BuiltinCmpGAction = { kind: "request", fn: "start" } | { kind: "request", fn: "next", args: [BuiltinCmpGState, any] };

function* builtin_cmp_g_impl(msg: BuiltinCmpGAction): Generator<any, any, any> {
  assert(msg.kind === "request");
  if (msg.fn === "start") {
    return { gen: builtin_cmp_g() };
  } else if (msg.fn === "next") {
    const [state, inner_msg] = msg.args;
    const result = state.gen.next(inner_msg);
    return [state, result];
  } else {
    throw Error("Bad message: " + JSON.stringify(msg));
  }
}


function* bind(gen: Generator<any, any, any>, fns: { [key: string]: (...args: any[]) => Generator<any, any, any> }): Generator<any, any, any> {
  let arg;
  while (true) {
    const action = gen.next(arg);
    if (action.done) {
      return action.value;
    }
    if (action.value.kind === "request") {
      const fn = fns[action.value.fn];
      if (fn === undefined) {
        throw Error("Bad function: " + action.value.fn);
      }
      arg = yield* fn(...action.value.args);
    } else {
      throw Error("Bad action: " + action.value.kind);
    }
  }
}

function* yield_and_bind(fn_name, args, handlers) {
  let cmp_op = yield { kind: "request", fn: fn_name, args: [{ kind: "request", fn: "start", args }] };

  let arg;
  while (true) {
    const [new_cmp_op, op_result] = yield {
      kind: "request", fn: fn_name, args: [{
        kind: "request", fn: "next", args: [cmp_op, arg]
      }]
    };
    cmp_op = new_cmp_op;
    if (op_result.done) {
      return op_result.value;
    }
    assert(op_result.value.kind === "request");

    const fn = handlers[op_result.value.fn];
    if (fn === undefined) {
      throw Error("Bad request: " + op_result.value);
    }
    arg = yield* fn(...op_result.value.args);
  }
}


function* yield_and_stateful_bind<S>(fn_name: string, args: any[], state: S, handlers: { [key: string]: (state: S, ...args: any[]) => Generator<any, [S, any], any> }): Generator<any, [S, any], any> {
  let cmp_op = yield { kind: "request", fn: fn_name, args: [{ kind: "request", fn: "start", args }] };

  let arg;
  while (true) {
    const [new_cmp_op, op_result] = yield {
      kind: "request", fn: fn_name, args: [{
        kind: "request", fn: "next", args: [cmp_op, arg]
      }]
    };
    cmp_op = new_cmp_op;
    if (op_result.done) {
      return [state, op_result.value];
    }
    assert(op_result.value.kind === "request");

    const fn = handlers[op_result.value.fn];
    if (fn === undefined) {
      throw Error("Bad request: " + op_result.value);
    }
    [state, arg] = yield* fn(state, ...op_result.value.args);
  }
}

function* stateful_bind<S>(gen: Generator<any, any, any>, state: S, fns: { [key: string]: (state: S, ...args: any[]) => Generator<any, [S, any], any> }): Generator<any, [S, any], any> {
  let arg;
  while (true) {
    const action = gen.next(arg);
    if (action.done) {
      return [state, action.value];
    }
    if (action.value.kind === "request") {
      const fn = fns[action.value.fn];
      if (fn === undefined) {
        throw Error("Bad function: " + action.value.fn);
      }
      [state, arg] = yield* fn(state, ...action.value.args);
    } else {
      throw Error("Bad action: " + action.value.kind);
    }
  }
}

describe("sort_list", () => {
  test("should work with bound", () => {
    function* bound_sort(arr) {
      return yield* stateful_bind(sort_list(), arr, {
        list: value_list_impl,
        *cmp(arr, msg) {
          return [arr, yield* builtin_cmp_g_impl(msg)];
        },
      });
    }
    const sort_list_op = bound_sort([3, 1, 2]);
    expect(sort_list_op.next().value).toEqual([[1, 2, 3], null]);
  });
});

type ord = '<' | '>' | '=';

function* iterator_cmp() {
  const a_has_next = yield { kind: "request", fn: "send_a", args: [{ kind: "request", fn: "next", args: [] }] };
  const b_has_next = yield { kind: "request", fn: "send_b", args: [{ kind: "request", fn: "next", args: [] }] };
  if (a_has_next && b_has_next) {
    const cmp_op = yield { kind: "request", fn: "item_cmp", args: [] };
    const result = yield* bind(cmp_op, {
      *send_a(msg) {
        return yield { kind: "request", fn: "send_a", args: [{ kind: "request", fn: "item", args: [msg] }] };
      },
      *send_b(msg) {
        return yield { kind: "request", fn: "send_b", args: [{ kind: "request", fn: "item", args: [msg] }] };
      },
    });
    if (result === '=') {
      return yield* iterator_cmp();
    } else {
      return result;
    }
  } else if (a_has_next) {
    return '>';
  } else if (b_has_next) {
    return '<';
  } else {
    return '=';
  }
}

function* iterable_cmp() {
  type IterPair = { a_iter: any, b_iter: any };

  const a_iter = yield { kind: "request", fn: "send_a", args: [{ kind: "request", fn: "new_iter", args: [] }] };
  const b_iter = yield { kind: "request", fn: "send_b", args: [{ kind: "request", fn: "new_iter", args: [] }] };
  const [spent_iters, result] = yield* stateful_bind<IterPair>(iterator_cmp(), { a_iter, b_iter }, {
    *send_a({ a_iter, b_iter }, msg): Generator<any, [IterPair, any], any> {
      assert(msg.kind === "request");
      if (msg.fn === "next") {
        const [new_a_iter, has_next] = yield { kind: "request", fn: "send_a", args: [{ kind: "request", fn: "iter_next", args: [a_iter] }] };
        return [{ a_iter: new_a_iter, b_iter: b_iter }, has_next];
      } else if (msg.fn === "item") {
        const [new_a_iter, resp] = yield { kind: "request", fn: "send_a", args: [{ kind: "request", fn: "iter_item", args: [a_iter, msg.args[0]] }] };
        return [{ a_iter: new_a_iter, b_iter: b_iter }, resp];
      } else {
        throw Error("Bad request: " + JSON.stringify(msg));
      }
    },
    *send_b({ a_iter, b_iter }, msg) {
      assert(msg.kind === "request");
      if (msg.fn === "next") {
        const [new_b_iter, has_next] = yield { kind: "request", fn: "send_b", args: [{ kind: "request", fn: "iter_next", args: [b_iter] }] };
        return [{ a_iter: a_iter, b_iter: new_b_iter }, has_next];
      } else if (msg.fn === "item") {
        const [new_b_iter, resp] = yield { kind: "request", fn: "send_b", args: [{ kind: "request", fn: "iter_item", args: [b_iter, msg.args[0]] }] };
        return [{ a_iter: a_iter, b_iter: new_b_iter }, resp];
      } else {
        throw Error("Bad request: " + JSON.stringify(msg));
      }
    },
    *item_cmp(state) {
      return [state, yield { kind: "request", fn: "item_cmp", args: [] }];
    },
  });
  return result;
}

function* list_iter_next(iter) {
  const index = iter.index + 1;
  if (index === iter.len) {
    return [{ index: index, len: iter.len }, false];
  } else {
    return [{ index: index, len: iter.len }, true];
  }
}

function* semi_bound_list_iterable_sort(list) {
  function* bound_iterable_cmp(): Generator<any, any, any> {
    return yield* bind(iterable_cmp(), {
      *send_a(msg) {
        return yield { kind: "request", fn: "send_a", args: [msg] };
      },
      *send_b(msg) {
        return yield { kind: "request", fn: "send_b", args: [msg] };
      },
      *item_cmp() {
        return builtin_cmp_g();
      },
    })
  }

  return yield* stateful_bind(sort_list(), list, {
    *list(list, msg) {
      return yield* bind(list_impl(list, msg), {
        item: value_list_impl,
      });
    },
    *cmp(list, msg) {
      assert(msg.kind === "request");
      if (msg.fn === "start") {
        return [list, { gen: bound_iterable_cmp() }];
      } else if (msg.fn === "next") {
        const [state, inner_msg] = msg.args;
        const result = state.gen.next(inner_msg);
        return [list, [state, result]];
      } else {
        throw Error("Bad message: " + JSON.stringify(msg));
      }
    },
  });
}

describe("sort list of lists of numbers", () => {
  test("compare lists", () => {
    const a = [1, 2];
    const b = [3, 1, 2];
    const op = stateful_bind(iterable_cmp(), { a, b }, {
      *send_a({ a, b }, msg) {
        const [new_a, resp] = yield* value_list_impl(a, msg);
        return [{ a: new_a, b }, resp];
      },
      *send_b({ a, b }, msg) {
        const [new_b, resp] = yield* value_list_impl(b, msg);
        return [{ a, b: new_b }, resp];
      },
      *item_cmp({ a, b }) {
        return [{ a, b }, builtin_cmp_g()];
      },
    }).next();
    expect(op.value[1]).toEqual('<');
  });

  test("should work", () => {
    const list = [
      [3, 1, 2],
      [1, 2, 3],
      [3, 1],
      [1, 2],
    ];
    const op = semi_bound_list_iterable_sort(list).next();
    expect(op.value[0]).toEqual([[1, 2], [1, 2, 3], [3, 1], [3, 1, 2]]);
    expect(op.value[1]).toBeNull();
  });
});

// type Action = { kind: string };
// type InputAction = { kind: "input", msg: any };
// type ResultAction<O> = { kind: "result", msg: O };
// type Machine<I extends Action, O extends Action> = (i: Action) => Action;

// function isInputAction(i: Action): i is InputAction {
//   return i.kind === "input";
// }

// function t<I, O>(f: (i: I) => O): Machine<InputAction, ResultAction<O>> {
//   return (i: Action) => {
//     if (!isInputAction(i)) {
//       throw Error("Bad action: " + i.kind);
//     }
//     return { kind: "result", msg: f(i.msg) };
//   }
// }

// function pair(self, action) {
//   const [a, b] = self;
//   if (action.kind === "send") {
//     if (action.target === "a") {
//       return [self, action.msg];
//     }
//     return [self, action.msg];
//   }
//   throw Error("Bad action: " + action.kind);
// }

// // function handleContinue<S>(machine: Function<S>, state: S, input: any): [S, string, any] {
// //   console.log("sending", machine.trace(state), JSON.stringify(input));
// //   let result = machine.run(state, input);
// //   while (result.action === 'continue') {
// //     state = result.resume_state;
// //     input = result.msg;
// //     console.log("handleContinue", machine.trace(state), JSON.stringify(input));

// //     result = machine.run(state, input);
// //   }
// //   console.log("recvd", JSON.stringify(result.msg));
// //   return [result.resume_state, result.action, result.msg];
// // }

// class FuncTranscript<S> {
//   machine: Function<S>;
//   state: S;
//   constructor(machine: Function<S>) {
//     this.machine = machine;
//     this.state = machine.init();
//   }

//   assertNext(input_action: string, input_msg: any, expected_action: string, expected_output: any) {
//     const [new_state, result] = this.machine.run(this.state, { action: input_action, msg: input_msg });
//     expect([result.action, result.msg]).toEqual([expected_action, expected_output]);
//     this.state = new_state;
//   }
// }

// // // function assertTransforms(machine: Machine<FuncState<unknown>>, input: any): any {
// // //   let result = machine(START_STATE, input);
// // //   while (result.action === 'continue') {
// // //     result = machine(result.resume_state, result.msg);
// // //   }
// // //   expect(result.action).toEqual('result');
// // //   return result.msg;
// // // }

// describe('Transformer', () => {
//   const machine = func("example", t((x: number) => x + 1));
//   test('should do the thing', () => {
//     const transcript = new FuncTranscript(machine);
//     transcript.assertNext('input', 2, 'result', 3);
//   });
// });

// const str_iter_init = func("str_iter_init", t((s: string) => [s, -1]));

// type StrIterState = [string, number];

// const str_iter2 = func(
//   "str_iter2",
//   t(([[str, offset], msg]: [StrIterState, ['next' | 'clone']]): [StrIterState, boolean | string] => {
//     if (msg[0] === 'next') {
//       offset += 1;
//       return [[str, offset], offset < str.length];
//     }
//     if (msg[0] === 'clone') {
//       return [[str, offset], str[offset]];
//     }
//     throw Error('Bad msg: ' + msg[0]);
//   }));

// describe('StrIter', () => {
//   test('should work with empty string', () => {
//     const transcript = new FuncTranscript(closure(str_iter_init, str_iter2));
//     transcript.assertNext('input', '', 'result', null);
//     transcript.assertNext('input', ['next'], 'result', false);
//   });

//   test('should work with non-empty string', () => {
//     const transcript = new FuncTranscript(closure(str_iter_init, str_iter2));
//     transcript.assertNext('input', 'foo', 'result', null);

//     transcript.assertNext('input', ['next'], 'result', true);
//     transcript.assertNext('input', ['clone'], 'result', 'f');
//     transcript.assertNext('input', ['next'], 'result', true);
//     transcript.assertNext('input', ['clone'], 'result', 'o');
//     transcript.assertNext('input', ['next'], 'result', true);
//     transcript.assertNext('input', ['clone'], 'result', 'o');
//     transcript.assertNext('input', ['next'], 'result', false);
//   });
// });

// type StringIterEqualsState = {
//   kind: "start"
// } | {
//   kind: "await_next",
//   str: string
// } | {
//   kind: "await_clone",
//   str: string
// } | {
//   kind: "end"
// };

// // const string_iter_equals: Function<StringIterEqualsState> = {
// //   name: "string_iter_equals",
// //   init() { return { kind: "start" }; },
// //   trace(state: StringIterEqualsState): string {
// //     return "string_iter_equals(" + state.kind + ")";
// //   },
// //   run(state: StringIterEqualsState, msg: Action<"input" | "resume", any>): [StringIterEqualsState, Action<"iter" | "result", any>] {
// //     if (state.kind === "start") {
// //       const s = msg.msg;
// //       return [{ kind: "await_next", str: s }, {
// //         action: "iter",
// //         msg: ["next"],
// //       }];
// //     }
// //     if (state.kind === "await_next") {
// //       const s = state.str;
// //       const [await_action, await_msg] = msg;
// //       if (await_action !== "result") {
// //         throw Error("Bad action: " + await_action);
// //       }
// //       const iter_has_next = await_msg;
// //       const str_has_next = s.length > 0;
// //       if (iter_has_next && str_has_next) {
// //         return {
// //           action: "iter",
// //           msg: ["clone"],
// //           resume_state: { kind: "await_clone", str: s },
// //         };
// //       }
// //       if (!iter_has_next && !str_has_next) {
// //         return {
// //           action: "result",
// //           msg: true,
// //           resume_state: { kind: "end" },
// //         };
// //       }
// //       // Otherwise: !iter_has_next || !str_has_next
// //       return {
// //         action: "result",
// //         msg: false,
// //         resume_state: { kind: "end" },
// //       };
// //     }
// //     if (state.kind === "await_clone") {
// //       const s = state.str;
// //       const [await_action, await_msg] = msg;
// //       if (await_action !== "result") {
// //         throw Error("Bad action: " + await_action);
// //       }
// //       const iter_char = await_msg;
// //       const str_char = s[0];
// //       if (iter_char === str_char) {
// //         return {
// //           action: "continue",
// //           msg: s.slice(1),
// //           resume_state: { kind: "start" },
// //         };
// //       } else {
// //         return {
// //           action: "result",
// //           msg: false,
// //           resume_state: { kind: "end" },
// //         };
// //       }
// //     }
// //     throw Error('Bad state: ' + state.kind);
// //   }
// // };

// // const string_iter_equals = func("string_iter_equals", sequence(
// //   t((s: string) => [s, {action: 'iter', msg: {action: 'next', msg: null}}]),
// //   call(str_iter_init, nullhandler),
// //   t(([s, str_iter]) => [str_iter, s]),
// //   call(string_iter_equals, string_iter_equals_handler2),
// //   t(([str_iter, result]) => result),
// // ));

// // describe('StringIterEquals', () => {
// //   test('should work with empty string', () => {
// //     const transcript = new FuncTranscript(string_iter_equals);
// //     transcript.assertNext('', 'iter', ['next']);
// //     transcript.assertNext(["result", false], 'result', true);
// //   });

// //   test('should work with non-empty string', () => {
// //     const transcript = new FuncTranscript(string_iter_equals);
// //     transcript.assertNext('foo', 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", 'f'], 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", 'o'], 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", 'o'], 'iter', ['next']);
// //     transcript.assertNext(["result", false], 'result', true);
// //   });

// //   test('should work with iter shorter than string', () => {
// //     const transcript = new FuncTranscript(string_iter_equals);
// //     transcript.assertNext('foo', 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", 'f'], 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", 'o'], 'iter', ['next']);
// //     transcript.assertNext(["result", false], 'result', false);
// //   });

// //   test('should work with string shorter than iter', () => {
// //     const transcript = new FuncTranscript(string_iter_equals);
// //     transcript.assertNext('foo', 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", 'f'], 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", 'o'], 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", 'o'], 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'result', false);
// //   });

// //   test('should work with char mismatch', () => {
// //     const transcript = new FuncTranscript(string_iter_equals);
// //     transcript.assertNext('foo', 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", 'f'], 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", 'r'], 'result', false);
// //   });
// // });

// // const string_iter_equals_handler2 = simpleHandler(sequence(
// //   t(([str_iter, [action, msg]]) => [[str_iter, msg], action]),
// //   match({
// //     iter: sequence(
// //       t(([str_iter, msg]) => [null, [str_iter, msg]]),
// //       call(str_iter2, defaultHandler),
// //       t(([_, [str_iter, msg]]) => [str_iter, msg])
// //     ),
// //     continue: sequence(
// //       t(([str_iter, msg]) => [str_iter, ["continue", msg]]),
// //       smuggle(raise),
// //       t(([str_iter, msg]) => [str_iter, msg]),
// //     )
// //   }),
// // ));

// // const string_iter_equals_inverse = func("string_iter_equals_inverse", sequence(
// //   t((s: string) => [s, s]),
// //   call(str_iter_init, defaultHandler),
// //   t(([s, str_iter]) => [str_iter, s]),
// //   call(string_iter_equals, string_iter_equals_handler2),
// //   t(([str_iter, result]) => result),
// // ));

// // describe('StringIterEqualsInverse', () => {
// //   test('should work with empty string', () => {
// //     const transcript = new FuncTranscript(string_iter_equals_inverse);
// //     transcript.assertNext('', 'result', true);
// //   });
// //   test('should work with non-empty string', () => {
// //     const transcript = new FuncTranscript(string_iter_equals_inverse);
// //     transcript.assertNext('foo', 'result', true);
// //   });
// // });

// // const char_iter_from_str_iter = func("char_iter_from_str_iter", sequence(
// //   // msg
// //   t((msg: any) => {
// //     if (msg[0] !== "next") {
// //       throw Error("Bad msg: " + msg);
// //     }
// //     return ["iter", ["next"]];
// //   }),
// //   raise,
// //   t((has_next: any) => [null, has_next]),
// //   if_then_else(
// //     sequence(
// //       t((_: any) => ["iter", ["clone"]]),
// //       raise,
// //       t((char: any) => ["some", char]),
// //     ),
// //     t((_: any) => ["none"]),
// //   )
// // ));


// // describe('CharIterFromStrIter', () => {
// //   test('unbound with empty string', () => {
// //     const transcript = new FuncTranscript(char_iter_from_str_iter);
// //     transcript.assertNext(['next'], 'iter', ['next']);
// //     transcript.assertNext(["result", false], 'result', ['none']);
// //   });
// //   test('unbound with non-empty string', () => {
// //     const transcript = new FuncTranscript(char_iter_from_str_iter);
// //     transcript.assertNext(['next'], 'iter', ['next']);
// //     transcript.assertNext(["result", true], 'iter', ['clone']);
// //     transcript.assertNext(["result", "f"], 'result', ['some', 'f']);
// //   });
// // });

// // const char_iter_from_string_init = func("char_iter_from_string_init", callNoRaise(str_iter_init));

// // const char_iter_from_string = func("char_iter_from_string",
// //   call(char_iter_from_str_iter, simpleHandler(sequence(t(([iter, [action, msg]]) => [[iter, msg], action]),
// //     match({
// //       iter: callNoRaise(str_iter2),
// //     }))),
// //   ));

// // // // const char_iter_from_string_closure = func(sequence(
// // // //   t((msg: any) => [msg, ["input", ["clone"]]]),
// // // //   smuggle(raise),
// // // //   call(char_iter_from_string_init, nullhandler),
// // // //   t(([msg, iter_state]: [any, CharIterFromStringState]) => [iter_state, msg]),
// // // //   loop( // [iter_state, msg]
// // // //     sequence(
// // // //       t(([iter_state, msg]: [CharIterFromStringState, any]) => [null, [iter_state, msg]]),
// // // //       call(char_iter_from_string, nullhandler),
// // // //       t(([_, [iter_state, msg]]: [any, [CharIterFromStringState, any]]) => [iter_state, msg]),
// // // //       smuggle(ret),
// // // //       t(([iter_state, msg]: [CharIterFromStringState, any]) => ["continue", [iter_state, msg]]),
// // // //     )
// // // //   )
// // // // ));

// // // const char_iter_from_string_closure = curryState(char_iter_from_string_init, char_iter_from_string);

// // // //   func(sequence(
// // // //   t((msg: any) => [msg, ["input", ["clone"]]]),
// // // //   smuggle(raise),
// // // //   call(char_iter_from_string_init, nullhandler),
// // // //   t(([msg, iter_state]: [any, CharIterFromStringState]) => [iter_state, msg]),
// // // //   loop( // [iter_state, msg]
// // // //     sequence(
// // // //       t(([iter_state, msg]: [CharIterFromStringState, any]) => [null, [iter_state, msg]]),
// // // //       call(char_iter_from_string, nullhandler),
// // // //       t(([_, [iter_state, msg]]: [any, [CharIterFromStringState, any]]) => [iter_state, msg]),
// // // //       smuggle(ret),
// // // //       t(([iter_state, msg]: [CharIterFromStringState, any]) => ["continue", [iter_state, msg]]),
// // // //     )
// // // //   )
// // // // ));

// // describe('CharIterFromString', () => {
// //   test('empty string', () => {
// //     const transcript = new FuncTranscript(closure(char_iter_from_string_init, char_iter_from_string));
// //     transcript.assertNext('', 'result', null);
// //     transcript.assertNext(['next'], 'result', ['none']);
// //   });
// //   test('non-empty string', () => {
// //     const transcript = new FuncTranscript(closure(char_iter_from_string_init, char_iter_from_string));
// //     transcript.assertNext('foo', 'result', null);
// //     transcript.assertNext(['next'], 'result', ['some', 'f']);
// //     transcript.assertNext(['next'], 'result', ['some', 'o']);
// //     transcript.assertNext(['next'], 'result', ['some', 'o']);
// //     transcript.assertNext(['next'], 'result', ['none']);
// //   });
// // });

// // // type SSVIterState = ["start"] | ["in_field"] | ["almost_finished"] | ["end"];

// // // const space_separated_value = func(withInit(["start"], closure(sequence(
// // //   t(([state, msg]: [SSVIterState, any]) =>
// // //     [[state, msg], state[0]]
// // //   ),
// // //   match({
// // //     start:
// // //       t(([state, msg]: [SSVIterState, any]) => {
// // //         if (msg[0] !== "next") {
// // //           throw Error("Bad msg: " + msg);
// // //         }
// // //         return [["in_field", ["none"]], true];
// // //       }),
// // //     in_field: sequence(
// // //       t(([state, msg]: [SSVIterState, any]) => {
// // //         if (msg[0] !== "inner_next") {
// // //           throw Error("Bad msg: " + msg);
// // //         }
// // //         return ["iter", ["next"]];
// // //       }),
// // //       raise,
// // //       t((next_char: ["some", string] | ["none"]) => [next_char, next_char[0] === "some"]),
// // //       if_then_else_null(
// // //         sequence(
// // //           t(([_, char]: ["some", string]) => [char, char === " "]),
// // //           if_then_else_null(
// // //             t((_: any) => [["start"], ["none"]]),
// // //             t((char: string) => [["in_field"], ["some", char]]),
// // //           ),
// // //         ),
// // //         t(([_]: ["none"]) => [["almost_finished"], ["none"]]),
// // //       ),
// // //     ),
// // //     almost_finished:
// // //       t(([state, msg]: [SSVIterState, any]) => {
// // //         if (msg[0] !== "next") {
// // //           throw Error("Bad msg: " + msg);
// // //         }
// // //         return [["end"], false];
// // //       }),
// // //   }),
// // // ))));

// // // const space_separated_value_for_string_init = func(sequence(
// // //   t((s: string) => [null, s]),
// // //   call(char_iter_from_string_init, nullhandler),
// // //   t(([_, iter_state]: [null, CharIterFromStringState]) => [iter_state, null]),
// // // ));


// // // const space_separated_value_for_string = func(
// // //   sequence(
// // //     t((msg: any) => [msg, ["input", ["clone"]]]),
// // //     call(char_iter_from_string_init, nullhandler),
// // //     t(([msg, iter_state]: [any, CharIterFromStringState]) => [iter_state, msg]),
// // //     smuggle(ret),
// // //     t(([iter_state, msg]: [CharIterFromStringState, any]) => ["continue", [iter_state, msg]]),
// // //   )
// // // );

// // // const space_separated_value_for_string_closure = curryState(space_separated_value_for_string_init, space_separated_value_for_string);

// // // // handle("iter", char_iter_from_string, space_separated_value);

// // // describe('SpaceSeparatedValue', () => {
// // //   // const closed = closure(space_separated_value_for_string);
// // //   test('empty string', () => {
// // //     // const init = assertTransforms(space_separated_value_for_string_init, "");

// // //     const transcript = new FuncTranscript(space_separated_value_for_string_closure);
// // //     transcript.assertNext(['next'], 'input', ['clone']);
// // //     transcript.assertNext('', 'result', true);

// // //     transcript.assertNext(['inner_next'], 'result', ['none']);
// // //     transcript.assertNext(['next'], 'result', false);
// // //   });
// // //   // test('one field', () => {
// // //   //   const init = assertTransforms(space_separated_value_for_string_init, "foo");

// // //   //   const transcript = new Transcript(space_separated_value_for_string, init);
// // //   //   transcript.assertNext(['next'], 'result', true);
// // //   //   transcript.assertNext(['inner_next'], 'result', ['some', 'f']);
// // //   //   transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
// // //   //   transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
// // //   //   transcript.assertNext(['inner_next'], 'result', ['none']);
// // //   //   transcript.assertNext(['next'], 'result', false);
// // //   // });

// // //   // test('double field', () => {
// // //   //   const init = assertTransforms(space_separated_value_for_string_init, "foo b");
// // //   //   const transcript = new Transcript(space_separated_value_for_string, init);
// // //   //   transcript.assertNext(['next'], 'result', true);
// // //   //   transcript.assertNext(['inner_next'], 'result', ['some', 'f']);
// // //   //   transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
// // //   //   transcript.assertNext(['inner_next'], 'result', ['some', 'o']);
// // //   //   transcript.assertNext(['inner_next'], 'result', ['none']);
// // //   //   transcript.assertNext(['next'], 'result', true);
// // //   //   transcript.assertNext(['inner_next'], 'result', ['some', 'b']);
// // //   //   transcript.assertNext(['inner_next'], 'result', ['none']);
// // //   //   transcript.assertNext(['next'], 'result', false);
// // //   // });
// // // });


// // const parse_int = func("parse_int", sequence(
// //   t((msg: null) => {
// //     if (msg !== null) {
// //       throw Error("Bad msg: " + msg);
// //     }
// //     return 0;
// //   }),
// //   loop(andThen(
// //     sequence(
// //       t((acc: number) => {
// //         return [acc, ["iter", ["next"]]];
// //       }),
// //       smuggle(raise),
// //       t(([acc, msg]: [number, any]) => {
// //         return [[acc, msg], msg[0] === "some"];
// //       })),
// //     if_then_else(
// //       andThen(
// //         t(([acc, char]: [number, ["some", string]]) => {
// //           return acc * 10 + (char[1].charCodeAt(0) - '0'.charCodeAt(0));
// //         }),
// //         next
// //       ),
// //       andThen(
// //         t(([acc, char]: [number, ["none"]]) => {
// //           return acc;
// //         }),
// //         brk,
// //       ),
// //     ),
// //   ))
// // ));

// // describe('ParseInt', () => {
// //   test('empty string', () => {
// //     const transcript = new FuncTranscript(parse_int);
// //     transcript.assertNext(null, 'iter', ['next']);
// //     transcript.assertNext(['result', ['none']], 'result', 0);
// //   });
// //   test('non-empty string', () => {
// //     const transcript = new FuncTranscript(parse_int);
// //     transcript.assertNext(null, 'iter', ['next']);
// //     transcript.assertNext(['result', ['some', '1']], 'iter', ['next']);
// //     transcript.assertNext(['result', ['some', '2']], 'iter', ['next']);
// //     transcript.assertNext(['result', ['some', '3']], 'iter', ['next']);
// //     transcript.assertNext(['result', ['none']], 'result', 123);
// //   });
// // });

// // // // const parse_int_from_string = sequence(
// // // //   char_iter_from_string_init,
// // // //   t((iter_state: CharIterFromStringState) => [[iter_state, null], null]),
// // // //   construct(handle("iter", char_iter_from_string, parse_int)),
// // // // );

// // // // describe('ParseIntFromString', () => {
// // // //   test('empty string', () => {
// // // //     const transcript = new Transcript(parse_int_from_string, null);
// // // //     transcript.assertNext("", 'result', 0);
// // // //   });
// // // //   test('non-empty string', () => {
// // // //     const transcript = new Transcript(parse_int_from_string, null);
// // // //     transcript.assertNext("1234", 'result', 1234);
// // // //   });
// // // // });

// // type IterMapState = "start" | "middle" | "end";

// // const iter_map_init = func("iter_map_init", t((_: null) => "start"));

// // const iter_map = func("iter_map", sequence(
// //   t(([state, msg]: [IterMapState, any]) => [[state, msg.slice(1)], msg[0]]),
// //   match({
// //     next: sequence(
// //       t(([_, rest]: [IterMapState, any[]]) => ["iter", ["next"]]),
// //       raise,
// //       t((has_next: boolean) => {
// //         if (has_next) {
// //           return ["middle", true];
// //         } else {
// //           return ["end", false];
// //         }
// //       }),
// //     ),
// //     item: sequence(
// //       t(([state, rest]: [IterMapState, any[]]) => {
// //         if (state !== "middle") {
// //           throw Error("Bad state: " + state);
// //         }
// //         return [null, rest[0]];
// //       }),
// //       raiseRaise("fn", simpleHandler(sequence(
// //         t(([_, [action, msg]]) => [msg, action]),
// //         match({
// //           input: sequence(
// //             t((msg: any) => ["iter", ["item", msg]]),
// //             raise,
// //             t((response: any) => [null, response]),
// //           ),
// //         }),
// //       ))
// //       ),
// //     ),
// //   })));

// // const doubler = func("doubler", sequence(
// //   t((msg: any) => {
// //     if (msg[0] !== "clone") {
// //       throw Error("Bad msg: " + msg);
// //     }
// //     return ["input", ["clone"]];
// //   }),
// //   raise,
// //   t((msg: number) => {
// //     return msg * 2;
// //   }),
// // ));

// // describe('IterMap', () => {
// //   test('empty iter', () => {
// //     const transcript = new FuncTranscript(closure(iter_map_init, iter_map));
// //     transcript.assertNext(null, 'result', null);
// //     transcript.assertNext(['next'], 'iter', ['next']);
// //     transcript.assertNext(['result', false], 'result', false);
// //   });
// //   test('double ints', () => {
// //     const transcript = new FuncTranscript(closure(iter_map_init, iter_map));
// //     transcript.assertNext(null, 'result', null);
// //     transcript.assertNext(['next'], 'iter', ['next']);
// //     transcript.assertNext(['result', true], 'result', true);
// //     transcript.assertNext(['item', ['clone']], 'fn', ['clone']);
// //     transcript.assertNext(['input', ['clone']], 'iter', ['item', ['clone']]);
// //     transcript.assertNext(['result', 3], 'fn', ['result', 3]);
// //     transcript.assertNext(['result', 6], 'result', 6);
// //     transcript.assertNext(['next'], 'iter', ['next']);
// //     transcript.assertNext(['result', false], 'result', false);
// //   });
// //   test('doubler', () => {
// //     const transcript = new FuncTranscript(doubler);
// //     transcript.assertNext(['clone'], 'input', ['clone']);
// //     transcript.assertNext(['result', 3], 'result', 6);
// //   });
// //   test('bind_doubler', () => {
// //     const bind_doubler_init = func("bind_doubler_init", callNoRaise(iter_map_init));
// //     const bind_doubler = func("bind_doubler", sequence(
// //       t(([mapped_state, msg]) => [null, [mapped_state, msg]]),
// //       call(iter_map, simpleHandler(sequence(
// //         t(([_, [action, msg]]) => [msg, action]),
// //         match({
// //           iter: sequence(
// //             t((msg: any) => ["iter", msg]),
// //             raise,
// //             t((response: any) => [null, response]),
// //           ),
// //           fn: sequence(
// //             t((msg: any) => [null, msg]),
// //             call(doubler, simpleHandler(sequence(
// //               t(([_, [action, msg]]) => [msg, action]),
// //               match({
// //                 input: sequence(
// //                   t((msg: any) => ["iter", ["item", msg]]),
// //                   raise,
// //                   t((response: any) => [null, response]),
// //                 ),
// //               }),
// //             ))),
// //           ),
// //         }),
// //       ))),
// //       t(([_, [mapped_state, msg]]) => [mapped_state, msg]),
// //     ));

// //     const transcript = new FuncTranscript(closure(bind_doubler_init, bind_doubler));
// //     transcript.assertNext(null, 'result', null);
// //     transcript.assertNext(['next'], 'iter', ['next']);
// //     transcript.assertNext(['result', true], 'result', true);
// //     transcript.assertNext(['item', ['clone']], 'iter', ['item', ['clone']]);
// //     transcript.assertNext(['result', 3], 'result', 6);
// //     transcript.assertNext(['next'], 'iter', ['next']);
// //     transcript.assertNext(['result', false], 'result', false);
// //   });
// // });
