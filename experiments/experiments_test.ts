// // // Test file for experiments.ts
// import { Machine, t, FuncFragment, func, Function, closure, Action } from './experiments';

import { assert } from "console";

type Thingy = {
  data: any,
  action: any,
  cb: any,
}

function int_impl(state, action) {
  if (state.kind === "start") {
    if (action.kind === "double") {
      return [state.data * 2, { kind: "result" }];
    } else if (action.kind === "stall_double") {
      return [{ kind: 'stall', data: state.data }, { kind: "continue" }];
    } else {
      throw Error("Bad action: " + action.kind);
    }
  } else if (state.kind === "stall") {
    if (action.kind === "resume") {
      return [state.data * 2, { kind: "result" }];
    } else {
      throw Error("Bad action: " + action.kind);
    }
  } else {
    throw Error("Bad state: " + state.kind);
  }
}


describe("int_impl", () => {
  test("should double", () => {
    let [state, action] = int_impl({ kind: 'start', data: 1 }, { kind: "double" });
    expect(action).toEqual({ kind: "result" });
    expect(state).toEqual(2);
  });

  test("should stall", () => {
    let [state, result] = int_impl({ kind: 'start', data: 1 }, { kind: "stall_double" });
    expect(result).toEqual({ kind: "continue" });

    [state, result] = int_impl(state, { kind: "resume" });
    expect(result).toEqual({ kind: "result" });
    expect(state).toEqual(2);
  });

});

function pair(state, action): [any, any] {
  if (state.kind === "start") {
    const [a, b] = state.data;
    if (action.kind === "a") {
      return [{ kind: 'a', b }, { kind: "request", target: "a", arg: a, action: action.inner }];
    } else if (action.kind === "b") {
      return [{ kind: 'b', a }, { kind: "request", target: "b", arg: b, action: action.inner }];
    } else {
      throw Error("Bad action: " + action.kind);
    }
  } else if (state.kind === "a") {
    if (action.kind === "reply") {
      return [[action.data, state.b], { kind: "result" }];
    } else {
      throw Error("Bad action: " + action.kind);
    }
  } else if (state.kind === "b") {
    if (action.kind === "reply") {
      return [[state.a, action.data], { kind: "result" }];
    } else {
      throw Error("Bad action: " + action.kind);
    }
  } else {
    throw Error("Bad state: " + state.kind);
  }
}

describe("pair", () => {
  test("should work", () => {

    // function test_case(root_cb) {
    let [state, action] = pair({ kind: 'start', data: [2, 3] }, { kind: "a", inner: { kind: "double" } });
    expect(action).toEqual({ kind: "request", target: "a", arg: 2, action: { kind: "double" } });

    let [int_state, int_action] = int_impl({ kind: "start", data: action.arg }, { kind: "double" });
    expect(int_action).toEqual({ kind: "result" });
    expect(int_state).toEqual(4);

    [state, action] = pair(state, { kind: "reply", data: int_state });

    expect(state).toEqual([4, 3]);
    expect(action).toEqual({ kind: "result" });
  });

  test("nested", () => {
    let [pair_state1, pair_action1] = pair({ kind: 'start', data: [[2, 3], 5] }, { kind: "a", inner: { kind: "b", inner: { kind: "double" } } });
    expect(pair_action1).toEqual({ kind: "request", target: "a", arg: [2, 3], action: { kind: "b", inner: { kind: "double" } } });

    let [pair_state2, pair_action2] = pair({ kind: 'start', data: pair_action1.arg }, pair_action1.action);
    expect(pair_action2).toEqual({ kind: "request", target: "b", arg: 3, action: { kind: "double" } });

    let [int_state2, int_action2] = int_impl({ kind: "start", data: pair_action2.arg }, pair_action2.action);
    expect(int_state2).toEqual(6);
    expect(int_action2).toEqual({ kind: "result" });

    let [pair_state3, pair_action3] = pair(pair_state2, { kind: "reply", data: int_state2 });
    expect(pair_state3).toEqual([2, 6]);
    expect(pair_action3).toEqual({ kind: "result" });

    let [pair_state4, pair_action4] = pair(pair_state1, { kind: "reply", data: pair_state3 });
    expect(pair_state4).toEqual([[2, 6], 5]);
    expect(pair_action4).toEqual({ kind: "result" });

  });
  // test("nested_stalling", () => {
  //   const pair_result1 = pair([[2, 3], 5], { kind: "a", inner: { kind: "b", inner: { kind: "double" } } });
  //   expect(pair_result1.data).toEqual([2, 3]);
  //   expect(, poll_a,ir_result2 = pair(pair_result1.data, pair_result1.action.action);
  //   expect(pair_result2.data).toBe(3);
  //   expect(pair_result2.action).toEqual({ kind: "request", target: "b", action: { kind: "double" } });

  //   const int_result1 = stalling_int_impl(pair_result2.data, pair_result2.action.action);
  //   expect(int_result1.action).toEqual({ kind: "result" });

  //   const int_result1_poll = stalling_int_impl_poll(int_result1.data, { kind: "resume" });
  //   expect(int_result1_poll.action).toEqual({ kind: "continue" });

  //   const int_result2_poll = stalling_int_impl_poll(int_result1_poll.data, { kind: "resume" });
  //   expect(int_result2_poll.data).toEqual(6);
  //   expect(int_result2_poll.action).toEqual({ kind: "result" });

  //   const pair_result4 = pair_result2.cb(int_result2_poll.data, { kind: "reply" });
  //   expect(pair_result4.data).toEqual([2, 6]);
  //   expect(pair_result4.action).toEqual({ kind: "result" });
  //   expect(pair_result4.cb).toBe(null);

  //   const pair_result5 = pair_result1.cb(pair_result4.data, { kind: "reply" });
  //   expect(pair_result5.data).toEqual([[2, 6], 5]);
  //   expect(pair_result5.action).toEqual({ kind: "result" });
  //   expect(pair_result5.cb).toBe(null);

  // });


  // function async_pair(data, action) {
  //   const result = pair(data, action);

  //   if (result.action.kind === "result") {
  //     return {data: result.data, action: result.action, cb: null};
  //   } else if (result.action.target === "a") {
  //     return {data: null, action: { kind: "request", target: "a", action: result.action.action }, cb: poll_a};
  //   } else if (result.action.target === "b") {
  //     return {data: null, action: { kind: "request", target: "b", action: result.action.action }, cb: poll_b};
  //   } else {
  //     throw Error("Bad action: " + JSON.stringify(result));
  //   }

  // }
  function bound_pair(handlers) {
    function call_a_request(state, action, pair_state, handler) {
      let [a_state, a_action] = handlers[handler](state, action);
      if (a_action.kind === "result") {
        return [{ kind: "resume_pair", data: a_state, pair_state }, { kind: "continue" }];
      } else if (a_action.kind === "continue") {
        return [{ kind: "await", handler, state: a_state, pair_state }, { kind: "continue" }];
      } else {
        throw Error("Bad Action: " + a_action.kind);
      }
    }
    function call_simple_pair(state, action) {
      let [pair_state, pair_action] = pair(state, action);
      if (pair_action.kind === "result") {
        return [pair_state, pair_action];
      } else if (pair_action.kind === "request") {
        if (pair_action.target === "a") {
          return call_a_request({ kind: "start", data: pair_action.arg }, pair_action.action, pair_state, "a");
        } else if (pair_action.target === "b") {
          return call_a_request({ kind: "start", data: pair_action.arg }, pair_action.action, pair_state, "b");
        } else {
          throw Error("Bad action: " + JSON.stringify(pair_action));
        }
      } else {
        throw Error("Bad State: " + state)
      }
    }
    return (state, action) => {
      if (state.kind === "start") {
        return call_simple_pair(state, action);
      } else if (state.kind === "resume_pair") {
        return call_simple_pair(state.pair_state, { kind: "reply", data: state.data });
      } else if (state.kind === "await") {
        return call_a_request(state.state, action, state.pair_state, state.handler);
      } else {
        throw Error("Bad State: " + state);
      }
    };
  }

  test("bound", () => {
    const bound = bound_pair({ a: int_impl, b: int_impl });
    let [pair_state1, pair_action1] = bound({ kind: "start", data: [2, 3] }, { kind: "a", inner: { kind: "double" } });
    expect(pair_action1).toEqual({ kind: "continue" });
    console.log(pair_state1);

    [pair_state1, pair_action1] = bound(pair_state1, pair_action1);
    expect(pair_action1).toEqual({ kind: "result" });
    expect(pair_state1).toEqual([4, 3]);
  });

  test("nested_bound", () => {
    const bound = bound_pair({ a: bound_pair({ a: int_impl, b: int_impl }), b: int_impl });

    let [pair_state1, pair_action1] = bound({ kind: "start", data: [[2, 3], 5] }, { kind: "a", inner: { kind: "b", inner: { kind: "double" } } });
    expect(pair_action1).toEqual({ kind: "continue" });

    [pair_state1, pair_action1] = bound(pair_state1, { kind: "resume" });
    expect(pair_action1).toEqual({ kind: "continue" });

    [pair_state1, pair_action1] = bound(pair_state1, { kind: "resume" });
    expect(pair_action1).toEqual({ kind: "result" });
    expect(pair_state1).toEqual([[2, 6], 5]);
  });

  test("nested_bound stalling", () => {
    const bound = bound_pair({ a: bound_pair({ a: int_impl, b: int_impl }), b: int_impl });

    let [pair_state1, pair_action1] = bound({ kind: "start", data: [[2, 3], 5] }, { kind: "a", inner: { kind: "b", inner: { kind: "stall_double" } } });
    expect(pair_action1).toEqual({ kind: "continue" });
    console.log(pair_state1);

    [pair_state1, pair_action1] = bound(pair_state1, { kind: "resume" });
    expect(pair_action1).toEqual({ kind: "continue" });

    [pair_state1, pair_action1] = bound(pair_state1, { kind: "resume" });
    expect(pair_action1).toEqual({ kind: "continue" });

    [pair_state1, pair_action1] = bound(pair_state1, { kind: "resume" });
    expect(pair_action1).toEqual({ kind: "result" });
    expect(pair_state1).toEqual([[2, 6], 5]);
  });
});

function coord(state, action) {
  if (action.kind === "x") {
    return pair(state, { kind: "a", inner: action.inner });
  } else if (action.kind === "y") {
    return pair(state, { kind: "b", inner: action.inner });
  } else {
    throw Error("Bad action: " + action.kind);
  }
}

function* poll_helper(target, action) {
  const op = yield { kind: "start", target, action }
  let poll_arg;
  while (true) {
    const get_min_action = yield { kind: "poll", target, state: op, action: poll_arg };
    if (get_min_action.done) {
      return get_min_action.value;
    }
    poll_arg = get_min_action.value;
  }
}

function* argmin_between_g(min, max): Generator<any, [any, number], any> {
  if (min === max) {
    return min;
  } else {
    let rec_argmin;
    rec_argmin = yield* argmin_between_g(min + 1, max);
    let min_ref;
    min_ref = yield { kind: "request", fn: "list_ref", args: [min] };
    let rec_ref;
    rec_ref = yield { kind: "request", fn: "list_ref", args: [rec_argmin] };
    const min_result = yield { kind: "request", fn: "cmp", args: [min_ref, rec_ref] };
    if (min_result === '<') {
      return min;
    } else {
      return rec_argmin;
    }
  }
}


describe("min_between", () => {
  test("should work", () => {
    const min_between_op = argmin_between_g(0, 3);
    expect(min_between_op.next().value).toEqual({ kind: "request", fn: "list_ref", args: [2] });
    expect(min_between_op.next(2).value).toEqual({ kind: "request", fn: "list_ref", args: [3] });
    expect(min_between_op.next(3).value).toEqual({ kind: "request", fn: "cmp", args: [2, 3] });
    expect(min_between_op.next('<').value).toEqual({ kind: "request", fn: "list_ref", args: [1] });
    expect(min_between_op.next(1).value).toEqual({ kind: "request", fn: "list_ref", args: [2] });
    expect(min_between_op.next(2).value).toEqual({ kind: "request", fn: "cmp", args: [1, 2] });
    expect(min_between_op.next('>').value).toEqual({ kind: "request", fn: "list_ref", args: [0] });
    expect(min_between_op.next(0).value).toEqual({ kind: "request", fn: "list_ref", args: [2] });
    expect(min_between_op.next(2).value).toEqual({ kind: "request", fn: "cmp", args: [0, 2] });
    expect(min_between_op.next('<').value).toEqual(0);
  });
});

function* sort_list_helper(start, end): Generator<any, any, any> {
  if (start === end) {
    return null;
  }
  const min = yield* argmin_between_g(start, end);
  yield { kind: "request", fn: "list_swap", args: [min, start] };
  return yield* sort_list_helper(start + 1, end);
}

function* sort_list(): Generator<any, null, any> {
  const len = yield { kind: "request", fn: "list_len", args: [] };
  return yield* sort_list_helper(0, len - 1);
}

function* with_ref(ref, fn) {
  const real_val = yield { kind: "request", fn: "ref_get", args: [ref] };
  const result = fn(real_val);
  yield { kind: "request", fn: "ref_set", args: [ref, real_val] };
  return result;
}

function* list_len(list) {
  return yield* with_ref(list, (list) => list.length);
}

function* list_ref(list, index) {
  return { kind: "index", list, index };
}

function* list_swap(list, index1, index2) {
  return yield* with_ref(list, (list) => {
    const tmp = list[index1];
    list[index1] = list[index2];
    list[index2] = tmp;
    return null;
  });
}

function* builtin_cmp(): any {
  const a_val = yield { kind: "request", fn: "get_a", args: [] };
  const b_val = yield { kind: "request", fn: "get_b", args: [] };
  let result;
  if (a_val < b_val) {
    result = '<';
  } else if (a_val > b_val) {
    result = '>';
  } else {
    result = '=';
  }
  yield { kind: "request", fn: "set_a", args: [a_val] };
  yield { kind: "request", fn: "set_b", args: [b_val] };
  return result;
}

function* bind(gen, fns) {
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

function* bound_builtin_cmp(a_ref, b_ref) {
  return yield* bind(builtin_cmp(), {
    *get_a() {
      return yield { kind: "request", fn: "ref_get", args: [a_ref] };
    },
    *get_b() {
      return yield { kind: "request", fn: "ref_get", args: [b_ref] };
    },
    *set_a(a_val) {
      return yield { kind: "request", fn: "ref_set", args: [a_ref, a_val] };
    },
    *set_b(b_val) {
      return yield { kind: "request", fn: "ref_set", args: [b_ref, b_val] };
    }
  });
}

describe("builtin_cmp", () => {
  test("should work", () => {
    const builtin_cmp_op = builtin_cmp();
    expect(builtin_cmp_op.next().value).toEqual({ kind: "request", fn: "get_a", args: [] });
    expect(builtin_cmp_op.next('a').value).toEqual({ kind: "request", fn: "get_b", args: [] });
    expect(builtin_cmp_op.next('b').value).toEqual({ kind: "request", fn: "set_a", args: ['a'] });
    expect(builtin_cmp_op.next(null).value).toEqual({ kind: "request", fn: "set_b", args: ['b'] });
    expect(builtin_cmp_op.next(null).value).toEqual('<');
  });

  test("should work with bound", () => {
    const builtin_cmp_op = bound_builtin_cmp('aref', 'bref');
    expect(builtin_cmp_op.next().value).toEqual({ kind: "request", fn: "ref_get", args: ['aref'] });
    expect(builtin_cmp_op.next('a').value).toEqual({ kind: "request", fn: "ref_get", args: ['bref'] });
    expect(builtin_cmp_op.next('b').value).toEqual({ kind: "request", fn: "ref_set", args: ['aref', 'a'] });
    expect(builtin_cmp_op.next(null).value).toEqual({ kind: "request", fn: "ref_set", args: ['bref', 'b'] });
    expect(builtin_cmp_op.next(null).value).toEqual('<');
  });
});

function* semi_bound_sort(list) {
  return yield* bind(sort_list(), {
    *list_len() {
      return yield* list_len(list);
    },
    *list_ref(index) {
      return yield* list_ref(list, index);
    },
    *list_swap(index1, index2) {
      return yield* list_swap(list, index1, index2);
    },
    *cmp(a, b) {
      return yield* bound_builtin_cmp(a, b);
    }
  });
}

function ns_ref_get(ns, ref) {
  if (ref.kind === "named") {
    if (ns[ref.name] === undefined) {
      throw Error("Bad named reference: " + ref.name);
    }
    const result = ns[ref.name];
    ns[ref.name] = undefined;
    return [ns, result];
  } else if (ref.kind === "index") {
    let list;
    [ns, list] = ns_ref_get(ns, ref.list);
    const result = list[ref.index];
    list[ref.index] = undefined;
    ns = ns_ref_set(ns, ref.list, list);
    return [ns, result];
  } else {
    throw Error("Bad reference: " + ref);
  }
}

function ns_ref_set(ns, ref, value) {
  if (ref.kind === "named") {
    ns[ref.name] = value;
    return ns;
  } else if (ref.kind === "index") {
    let list;
    [ns, list] = ns_ref_get(ns, ref.list);
    list[ref.index] = value;
    return ns_ref_set(ns, ref.list, list);
  }
}
function* ref_space(ns, gen) {
  let arg;
  while (true) {
    const action = gen.next(arg);
    if (action.done) {
      return [ns, action.value];
    }
    if (action.value.kind === "request") {
      if (action.value.fn === "ref_get") {
        const [new_ns, result] = ns_ref_get(ns, action.value.args[0]);
        ns = new_ns;
        arg = result;
      } else if (action.value.fn === "ref_set") {
        ns = ns_ref_set(ns, action.value.args[0], action.value.args[1]);
        arg = null;
      } else {
        throw Error("Bad function: " + action.value.fn);
      }
    } else {
      throw Error("Bad action: " + action.value.kind);
    }
  }
}

function* bound_sort(arr) {
  const gen = semi_bound_sort({ kind: "named", name: "thelist" });
  const [new_ns, result] = yield* ref_space({
    "thelist": arr,
  }, gen);
  return new_ns["thelist"];
}

describe("sort_list", () => {
  test("should work", () => {
    const sort_list_op = sort_list();
    expect(sort_list_op.next().value).toEqual({ kind: "request", fn: "list_len", args: [] });
    expect(sort_list_op.next(3).value).toEqual({ kind: "request", fn: "list_ref", args: [1] });
    expect(sort_list_op.next('r1').value).toEqual({ kind: "request", fn: "list_ref", args: [2] });
    expect(sort_list_op.next('r2').value).toEqual({ kind: "request", fn: "cmp", args: ['r1', 'r2'] });
    expect(sort_list_op.next('<').value).toEqual({ kind: "request", fn: "list_ref", args: [0] });
    expect(sort_list_op.next('r0').value).toEqual({ kind: "request", fn: "list_ref", args: [1] });
    expect(sort_list_op.next('r1').value).toEqual({ kind: "request", fn: "cmp", args: ['r0', 'r1'] });
    expect(sort_list_op.next(">").value).toEqual({ kind: "request", fn: "list_swap", args: [1, 0] });
    expect(sort_list_op.next(null).value).toEqual({ kind: "request", fn: "list_ref", args: [1] });
    expect(sort_list_op.next('r1').value).toEqual({ kind: "request", fn: "list_ref", args: [2] });
    expect(sort_list_op.next('r2').value).toEqual({ kind: "request", fn: "cmp", args: ['r1', 'r2'] });
    expect(sort_list_op.next('>').value).toEqual({ kind: "request", fn: "list_swap", args: [2, 1] });
    expect(sort_list_op.next(null).value).toEqual(null);
  });

  test("should work with bound", () => {
    const sort_list_op = bound_sort([3, 1, 2]);
    expect(sort_list_op.next().value).toEqual([1, 2, 3]);
  });
});

type ord = '<' | '>' | '=';

function* iterator_cmp(a, b, cmp) {
  let a_has_next, b_has_next;
  [a, a_has_next] = yield { kind: "request", fn: "a_next", args: [a] };
  [b, b_has_next] = yield { kind: "request", fn: "b_next", args: [b] };
  if (a_has_next && b_has_next) {
    let a_item, b_item;
    [a, a_item] = yield { kind: "request", fn: "a_item", args: [a] };
    [b, b_item] = yield { kind: "request", fn: "b_item", args: [b] };
    const result = yield { kind: "request", fn: "cmp", args: [cmp, a_item, b_item] };
    return [a, b, cmp, result];
  } else if (a_has_next) {
    return [a, b, cmp, '>'];
  } else if (b_has_next) {
    return [a, b, cmp, '<'];
  } else {
    return [a, b, cmp, '='];
  }
}

function* iterable_cmp(a, b, cmp) {
  let a_iter, b_iter;
  [a, a_iter] = yield { kind: "request", fn: "a_iter", args: [a] };
  [b, b_iter] = yield { kind: "request", fn: "b_iter", args: [b] };
  return yield* iterator_cmp(a_iter, b_iter, cmp);
}

function* number_cmp(a, b) {
  if (a < b) {
    return '<';
  } else if (a > b) {
    return '>';
  } else {
    return '=';
  }
}

// a: char_iter
// b: char_iter
function* strcmp() {
  const a = yield { kind: "request", target: "a", action: { kind: "next" } };
  const b = yield { kind: "request", target: "b", action: { kind: "next" } };
  if (a[0] === 'none' && b[0] === 'none') {
    return '=';
  } else if (a[0] === 'none') {
    return '<';
  } else if (b[0] === 'none') {
    return '>';
  } else {
    const a_char = a[1];
    const b_char = b[1];
    if (a_char < b_char) {
      return '<';
    } else if (a_char > b_char) {
      return '>';
    } else {
      return yield* strcmp();
    }
  }
}

function* ref_slice_impl(arr, action) {
  if (action.kind === "item") {
    const offset = action.offset;
    const [item, result] = yield { kind: "request", target: "item", state: arr[offset], action: action.inner };
    arr[offset] = item;
    return [arr, result];
  }
  throw Error("Bad action: " + action.kind);
}

function* value_slice_impl(arr, action) {
  if (action.kind === "iter") {
    return [arr, [-1, arr.length]];
  } else if (action.kind === "item") {
    const offset = action.offset;
    return [arr, arr[offset]];
  }
  throw Error("Bad action: " + action.kind);
}

function* value_slice_iter_impl([offset, len], action) {
  if (action.kind === "next") {
    if (offset === len) {
      return [null, ['none']];
    } else {
      const item = yield { kind: "request", target: "slice", action: { kind: "item", data: offset } };
      return [offset + 1, ['some', item]];
    }
  }
  throw Error("Bad action: " + action.kind);
}

describe("slice_of_slice_of_numbers", () => {
  test("manual", () => {
    const data = [[1, 2, 3], [4, 5, 6]];

    const get_value_op = ref_slice_impl(data, { kind: "item", offset: 0, inner: { kind: "item", offset: 2 } });
    expect(get_value_op.next().value).toEqual({ kind: "request", target: "item", state: [1, 2, 3], action: { kind: "item", offset: 2 } });
    expect(get_value_op.next([[1, 2, 3], 3]).value).toEqual([[[1, 2, 3], [4, 5, 6]], 3]);
  });
  test("manual delegation", () => {
    const data = [[1, 2, 3], [4, 5, 6]];

    const get_value_op = ref_slice_impl(data, { kind: "item", offset: 0, inner: { kind: "item", offset: 2 } });
    expect(get_value_op.next().value).toEqual({ kind: "request", target: "item", state: [1, 2, 3], action: { kind: "item", offset: 2 } });
    const value_slice_op = value_slice_impl([1, 2, 3], { kind: "item", offset: 2 });
    expect(value_slice_op.next().value).toEqual([[1, 2, 3], 3]);
    expect(get_value_op.next([[1, 2, 3], 3]).value).toEqual([[[1, 2, 3], [4, 5, 6]], 3]);
  });
  test("binding", () => {
    function* bound(state, action) {
      const op = ref_slice_impl(state, action);
      let arg;
      while (true) {
        const resp: any = op.next(arg);
        if (resp.done) {
          return resp.value;
        }
        if (resp.value.kind === "request") {
          if (resp.value.target === "item") {
            arg = yield* value_slice_impl(resp.value.state, resp.value.action);
          } else {
            throw Error("Bad target: " + resp.value.target);
          }
        } else {
          throw Error("Bad action: " + resp.value.kind);
        }
      }
    }


    const data = [[1, 2, 3], [4, 5, 6]];

    const get_value_op = bound(data, { kind: "item", offset: 0, inner: { kind: "item", offset: 2 } });
    expect(get_value_op.next().value).toEqual([[[1, 2, 3], [4, 5, 6]], 3]);
  });

  test("iter", () => {
    const data = [[1, 2, 3], [4, 5, 6]];

    const get_iter_op = ref_slice_impl(data, { kind: "item", offset: 0, inner: { kind: "iter" } });
    expect(get_iter_op.next().value).toEqual({ kind: "request", target: "item", state: [1, 2, 3], action: { kind: "iter" } });
    expect(get_iter_op.next([[1, 2, 3], [-1, 3]]).value).toEqual([[[1, 2, 3], [4, 5, 6]], [-1, 3]]);

    const iter = [-1, 3];
  });
});

// function* str_iter_impl(str: string, action) {
//   if (action.kind === "next") {
//     if (str.length === 0) {
//       return [null, ['none']];
//     } else {
//       return [str.slice(1), ['some', str[0]]];
//     }
//   }
//   throw Error("Bad action: " + action.kind);
// }

// function* str_impl(str: string, action) {
//   if (action.kind === "iter") {
//     return str_iter_impl(str, action);
//   }
//   throw Error("Bad action: " + action.kind);
// }

// function* str() {
//   const str = yield {kind: "request", target: "str", action: {kind: "next"}};
//   return yield* str_iter_impl(str, action);
// }

// describe("strcmp", () => {
//   test("should work", () => {
//     const strcmp_op = strcmp();
//     expect(strcmp_op.next().value).toEqual({kind: "request", target: "a", action: {kind: "next"}});
//     expect(strcmp_op.next(['none']).value).toEqual({kind: "request", target: "b", action: {kind: "next"}});
//     expect(strcmp_op.next(['none']).value).toEqual('=');
//   });
// });

type Action = { kind: string };
type InputAction = { kind: "input", msg: any };
type ResultAction<O> = { kind: "result", msg: O };
type Machine<I extends Action, O extends Action> = (i: Action) => Action;

function isInputAction(i: Action): i is InputAction {
  return i.kind === "input";
}

function t<I, O>(f: (i: I) => O): Machine<InputAction, ResultAction<O>> {
  return (i: Action) => {
    if (!isInputAction(i)) {
      throw Error("Bad action: " + i.kind);
    }
    return { kind: "result", msg: f(i.msg) };
  }
}

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
