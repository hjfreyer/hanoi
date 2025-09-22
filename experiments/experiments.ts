import assert from "assert";

export const START_STATE : START_STATE_TYPE = {kind: "start"};

type START_STATE_TYPE =  {kind: "start"};

type FUNC_ACTION_TYPE = "continue" | "result" | "return" | "raise";

export type FuncFragmentContext = {
  locals: Record<string, any>;
  stack: any[];
}

export type FuncFragmentResult<S> = {
  action: FUNC_ACTION_TYPE;
  resume_state: S;
  msg: any;
};

export type FuncFragment<S> = (state: Startable<S>, msg: any) => FuncFragmentResult<S>;

export type Func2State<S> = ["start"] | ["inner", Startable<S>];

export function func2<S>(inner: FuncFragment<S>): Machine<Func2State<S>> {
  return (state: Func2State<S>, msg: any): Result<Func2State<S>> => {
    if (state[0] === "start") {
      return { action: "continue", msg, resume_state: ["inner", START_STATE] };
    }
    if (state[0] === "inner") {
      const inner_state = state[1];
      const result = inner(inner_state, msg);
      if (result.action === "result" || result.action === "continue") {
        return { action: result.action, msg: result.msg, resume_state: ["inner", result.resume_state] };
      }
      if (result.action === "return") {
        return { action: "result", msg: result.msg, resume_state: ["inner", result.resume_state] };
      }
      if (result.action === "raise") {
        const [action, inner_msg] = result.msg;
        return { action: action, msg: inner_msg, resume_state: ["inner", result.resume_state] };
      }
      throw Error("Bad action: " + result.action);
    }
    throw Error("Bad state: " + state[0]);
  };
}

export type SingleStateResult = {
  action: FUNC_ACTION_TYPE;
  msg: any;
}

export function singleState(func : (msg: any) =>SingleStateResult  ): FuncFragment<START_STATE_TYPE> {
  return (state: Startable<START_STATE_TYPE>, msg: any) => {
    const new_result = func(msg);
    return { action: new_result.action, resume_state: START_STATE, msg: new_result.msg };
  };
}

export function bind(name: string): FuncFragment<START_STATE_TYPE> {
  return singleState((msg: any) => {
    const context : FuncFragmentContext = msg;
    const top = context.stack.pop();
    return { action: "result", msg: {locals: {name: top, ...context.locals}, stack: context.stack} };
  });
}



export type Result<S> = {
  action: string;
  msg: any;
  resume_state: S;
};

export type Machine<S> = (state: S, msg: any) => Result<S>;

export type Combinator<I, S> = {
  init(arg: I): S;
  run(state: S, msg: any): Result<S>;
};

export type FuncState<S> = ["start"] | ["inner", S];

export function func<S>(inner: Combinator<null, S>): Machine<FuncState<S>> {
  return (state: FuncState<S>, msg: any): Result<FuncState<S>> => {
    if (state[0] === "start") {
      return { action: "continue", msg, resume_state: ["inner", inner.init(null)] };
    }
    if (state[0] === "inner") {
      const inner_state = state[1];
      const result = inner.run(inner_state, msg);
      if (result.action === "result" || result.action === "continue") {
        return { action: result.action, msg: result.msg, resume_state: ["inner", result.resume_state] };
      }
      if (result.action === "return") {
        return { action: "result", msg: result.msg, resume_state: ["inner", result.resume_state] };
      }
      if (result.action === "raise") {
        const [action, inner_msg] = result.msg;
        return { action: action, msg: inner_msg, resume_state: ["inner", result.resume_state] };
      }
      throw Error("Bad action: " + result.action);
    }
    throw Error("Bad state: " + state[0]);
  };
}

type CallState<H, A, C> = ["start", FuncState<C>] | ["inner", A, FuncState<C>] | ["handler", H, FuncState<C>];

export function call<H, A, C>(callee: Machine<FuncState<C>>, handler: Combinator<null, H>): Combinator<null, CallState<H, A, C>> {
  return {
    init(_: null): CallState<H, A, C> {
      return ["start", ["start"]];
    },
    run(state: CallState<H, A, C>, msg: any): Result<CallState<H, A, C>> {
      if (state[0] === "start") {
        const inner_state = state[1];
        const [handler_arg, inner_arg] = msg;
        return { action: "continue", msg: inner_arg, resume_state: ["inner", handler_arg, inner_state] };
      }
      if (state[0] === "inner") {
        const handler_arg = state[1];
        const inner_state = state[2];
        const result = callee(inner_state, msg);
        if (result.action === "result") {
          return { action: "result", msg: [handler_arg, result.msg], resume_state: ["start", result.resume_state] };
        } else if (result.action === "continue") {
          return { action: "continue", msg: result.msg, resume_state: ["inner", handler_arg, result.resume_state] };
        } else {
          return { action: "continue", msg: [handler_arg, result.action, result.msg], resume_state: ["handler", handler.init(null), result.resume_state] };
        }
      }
      if (state[0] === "handler") {
        const handler_state = state[1];
        const inner_state = state[2];
        const result = handler.run(handler_state, msg);
        if (result.action === "result") {
          const [handler_arg, inner_arg] = result.msg;
          return { action: "continue", msg: inner_arg, resume_state: ["inner", handler_arg, inner_state] };
        }
        if (result.action === "continue") {
          return { action: "continue", msg: result.msg, resume_state: ["handler", result.resume_state, inner_state] };
        }
        if (result.action === "raise") {
          return { action: "raise", msg: result.msg, resume_state: ["handler", result.resume_state, inner_state] };
        }
        throw Error("Bad action: " + result.action);
      }
      throw Error("Bad state: " + state[0]);
    }
  };
}

export function t(f: (msg: any) => any): Combinator<null, ["start"]> {
  return {
    init(_: null): ["start"] {
      return ["start"];
    },
    run(state: ["start"], msg: any): Result<["start"]> {
      assert(state[0] === "start", "Bad state: " + state[0]);
      return {
        action: "result",
        msg: f(msg),
        resume_state: state,
      };
    }
  };
}


export type AndThenState<F, G> = ["first", F, G] | ["second", G];

export type Startable<T> = T | START_STATE_TYPE;

export function andThenInit<F, G>(f: F, g: G): AndThenState<F, G> {
  return ["first", f, g];
}

export function andThen<F, G>(f: Machine<F>, g: Machine<G>): Machine<AndThenState<F, G>> {
  return (state: AndThenState<F, G>, msg: any): Result<AndThenState<F, G>> => {
    if (state[0] === "first") {
      let f_state = state[1];
      let g_state = state[2];
      const result = f(f_state, msg);
      if (result.action === "result") {
        return { action: "continue", msg: result.msg, resume_state: ["second", g_state] };
      }
      return { action: result.action, msg: result.msg, resume_state: ["first", result.resume_state, g_state] };
    }
    if (state[0] === "second") {
      let g_state = state[1];
      const result = g(g_state, msg);
      return { action: result.action, msg: result.msg, resume_state: ["second", result.resume_state] };
    }
    throw Error("Bad state: " + state[0]);
  };
}


export type SequenceState = [number, unknown[]];



export function sequence<I>(first: Combinator<I, unknown>, ...rest: Combinator<null, unknown>[]) {
  return {
    init(arg: I): SequenceState {
      return [0, [first.init(arg), ...rest.map((c) => c.init(null))]];
    },
    run(state: SequenceState, msg: any): Result<SequenceState> {
      let index = state[0];
      let states = state[1];

      const [current_state, ...states_rest] = states;
      const result = [first.run, ...rest.map((c) => c.run)][index](current_state, msg);
      if (result.action === "result") {
        index += 1;
        if (index < [first.run, ...rest.map((c) => c.run)].length) {
          return { action: "continue", msg: result.msg, resume_state: [index, states_rest] };
        } else {
          return { action: "result", msg: result.msg, resume_state: [-1, []] };
        }
      }
      return { action: result.action, msg: result.msg, resume_state: [index, [result.resume_state, ...states_rest]] };
    }
  };
}


export type SmuggleState<S> = ["ready", S] | ["inner", unknown, S];


export function smuggle<I, S>(inner: Combinator<I, S>): Combinator<I, SmuggleState<S>> {
  return {
    init(arg: I): SmuggleState<S> {
      return ["ready", inner.init(arg)];
    },
    run(state: SmuggleState<S>, msg: any): Result<SmuggleState<S>> {
      if (state[0] === "ready") {
        const inner_state = state[1];
        const [smuggle, inner_msg] = msg;
        return { action: "continue", msg: inner_msg, resume_state: ["inner", smuggle, inner_state] };
      }
      if (state[0] === "inner") {
        const smuggle = state[1];
        const inner_state = state[2];
        const result = inner.run(inner_state, msg);
        if (result.action === "result") {
          return { action: "result", msg: [smuggle, result.msg], resume_state: ["ready", result.resume_state] };
        }
        if (result.action === "return") {
          return { action: "return", msg: result.msg, resume_state: ["inner", smuggle, result.resume_state] };
        }
        if (result.action === "continue") {
          return { action: "continue", msg: result.msg, resume_state: ["inner", smuggle, result.resume_state] };
        }
        if (result.action === "raise") {
          return { action: "raise", msg: result.msg, resume_state: ["inner", smuggle, result.resume_state] };
        }
        throw Error("Bad action: " + result.action);
      }
      throw Error("Bad state: " + state[0]);
    }
  };
}

export type MatchCases<I, H> = { [K in keyof H]: Combinator<I, H[K]> };
export type MatchState<I, H> = ["start", I] | ["within", keyof H, H[keyof H]];

export function match<I, H>(cases: MatchCases<I, H>): Combinator<I, MatchState<I, H>> {
  return {
    init(arg: I): MatchState<I, H> {
      return ["start", arg];
    },
    run(state: MatchState<I, H>, msg: any): Result<MatchState<I, H>> {
      if (state[0] === "start") {
        let arg = state[1];
        let [outer_state, selector]: [any, keyof H] = msg;
        return { action: "continue", msg: outer_state, resume_state: ["within", selector, cases[selector].init(arg)] };
      }
      if (state[0] === "within") {
        let selector = state[1];
        let inner_state = state[2];
        if (!(selector in cases)) {
          throw Error("Bad selector: " + String(selector));
        }
        const result = cases[selector].run(inner_state, msg);
        return { action: result.action, msg: result.msg, resume_state: ["within", selector, result.resume_state] };
      }
      throw Error("Bad state: " + state[0]);
    }
  }
}

type RaiseState = ["start"] | ["await_raise"] | ["end"];

export const raise: Combinator<null, RaiseState> = {
  init(_: null): RaiseState {
    return ["start"];
  },
  run(state: RaiseState, msg: any): Result<RaiseState> {
    if (state[0] === "start") {
      return {
        action: "raise",
        msg: msg,
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
};

type RetState = ["start"] | ["await_return"] | ["end"];

export const ret: Combinator<null, RetState> = {
  init(_: null): RetState {
    return ["start"];
  },
  run(state: RetState, msg: any): Result<RetState> {
    if (state[0] === "start") {
      return {
        action: "return",
        msg: msg,
        resume_state: ["await_return"],
      };
    }
    if (state[0] === "await_return") {
      return {
        action: "result",
        msg: msg,
        resume_state: ["end"],
      };
    }
    throw Error('Bad state: ' + state[0]);
  }
};

export type IfThenElseState<T, F> = ["start", T, F] | ["then", T] | ["else", F];

function if_then_else_impl<T, F>(then: Machine<T>, els: Machine<F>): Machine<IfThenElseState<T, F>> {
  return function if_then_else_impl(state: IfThenElseState<T, F>, msg: any): Result<IfThenElseState<T, F>> {
    if (state[0] === "start") {
      let then_state = state[1];
      let els_state = state[2];
      let [outer_state, cond] = msg;
      if (cond) {
        return {
          action: "continue",
          msg: outer_state,
          resume_state: ["then", then_state],
        };
      } else {
        return {
          action: "continue",
          msg: outer_state,
          resume_state: ["else", els_state],
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

export function if_then_else<IT, T, IF, F>(then: Combinator<IT, T>, els: Combinator<IF, F>): Combinator<[IT, IF], IfThenElseState<T, F>> {
  return {
    init([arg_t, arg_f]: [IT, IF]): IfThenElseState<T, F> {
      return ["start", then.init(arg_t), els.init(arg_f)];
    },
    run(state: IfThenElseState<T, F>, msg: any): Result<IfThenElseState<T, F>> {
      return if_then_else_impl(then.run, els.run)(state, msg);
    }
  };
}
export function if_then_else_null<T, F>(then: Combinator<null, T>, els: Combinator<null, F>): Combinator<null, IfThenElseState<T, F>> {
  return {
    init(_: null): IfThenElseState<T, F> {
      return ["start", then.init(null), els.init(null)];
    },
    run(state: IfThenElseState<T, F>, msg: any): Result<IfThenElseState<T, F>> {
      return if_then_else_impl(then.run, els.run)(state, msg);
    }
  };
}

export type ClosureState<C, S> = ["ready", C] | ["inner", S];


export function closure<C, S>(inner: Combinator<null, S>): Combinator<C, ClosureState<C, S>> {
  return {
    init(closure: C): ClosureState<C, S> {
      return ["ready", closure];
    },
    run(state: ClosureState<C, S>, msg: any): Result<ClosureState<C, S>> {
      if (state[0] === "ready") {
        const closure = state[1];
        return {
          action: "continue",
          msg: [closure, msg],
          resume_state: ["inner", inner.init(null)],
        }
      }
      if (state[0] === "inner") {
        const inner_state = state[1];
        const result = inner.run(inner_state, msg);
        if (result.action === "result") {
          const [new_closure, new_output] = result.msg;
          return {
            action: "result",
            msg: new_output,
            resume_state: ["ready", new_closure],
          };
        }
        return {
          action: result.action,
          msg: result.msg,
          resume_state: ["inner", result.resume_state],
        };
      }
      throw Error('Bad state: ' + state[0]);
    }
  };
}

export function withInit<I, S>(value: I, inner: Combinator<I, S>): Combinator<null, S> {
  return {
    init(arg: null): S {
      return inner.init(value);
    },
    run(state: S, msg: any): Result<S> {
      return inner.run(state, msg);
    }
  };
}

export type LoopState<S> = ["inner", S] | ["end"];
export function loop<S>(inner: Combinator<null, S>): Combinator<null, LoopState<S>> {
  return {
    init(_: null): LoopState<S> {
      return ["inner", inner.init(null)];
    },
    run(state: LoopState<S>, msg: any): Result<LoopState<S>> {
      if (state[0] === "inner") {
        const result = inner.run(state[1], msg);
        if (result.action === "result") {
          const [inner_action, inner_msg] = result.msg;
          if (inner_action === "break") {
            return { action: "result", msg: inner_msg, resume_state: ["end"] };
          }
          if (inner_action === "continue") {
            return { action: "continue", msg: inner_msg, resume_state: ["inner", inner.init(null)] };
          }
          throw Error('Bad inner action: ' + inner_action);
        }
        if (result.action === "return" || result.action === "raise" || result.action === "continue") {
          return { action: result.action, msg: result.msg, resume_state: ["inner", result.resume_state] };
        }
        throw Error('Bad action: ' + result.action);
      }
      throw Error('Bad state: ' + state[0]);
    }
  };
}

export type HandleState<H, I> = ["inner", H, I] | ["handler", H, I] | ["end"];

export function handle<HI, H, II, I>(action: string, handler: Combinator<HI, H>, inner: Combinator<II, I>): Combinator<[HI, II], HandleState<H, I>> {
  return {
    init(arg: [HI, II]) {
      return ["inner", handler.init(arg[0]), inner.init(arg[1])];
    },
    run(state: HandleState<H, I>, msg: any): Result<HandleState<H, I>> {
      if (state[0] === "inner") {
        const handler_state = state[1];
        const inner_state = state[2];
        const result = inner.run(inner_state, msg);
        if (result.action === action) {
          return { action: "continue", msg: result.msg, resume_state: ["handler", handler_state, result.resume_state] };
        }
        return { action: result.action, msg: result.msg, resume_state: ["inner", handler_state, result.resume_state] };
      }
      if (state[0] === "handler") {
        const handler_state = state[1];
        const inner_state = state[2];
        const result = handler.run(handler_state, msg);
        if (result.action === "result") {
          return { action: "continue", msg: result.msg, resume_state: ["inner", result.resume_state, inner_state] };
        }
        return { action: result.action, msg: result.msg, resume_state: ["handler", result.resume_state, inner_state] };
      }
      throw Error('Bad state: ' + state[0]);
    }
  };
}

export type ConstructState<S> = ["start"] | ["inner", S];

export function construct<S>(inner: Combinator<unknown, S>): Combinator<null, ConstructState<S>> {
  return {
    init(_: null): ConstructState<S> {
      return ["start"];
    },
    run(state: ConstructState<S>, msg: any): Result<ConstructState<S>> {
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

type CurryState<I, S> = ["await_init", unknown] | ["transform_init", FuncState<I>, unknown] | ["inner", FuncState<S>] | ["ready", FuncState<S>, unknown];

export function curryState<I, S>(stateInit: Machine<FuncState<I>>, machine: Machine<FuncState<S>>): Machine<FuncState<CurryState<I, S>>> {
  return (state: FuncState<CurryState<I, S>>, msg: any): Result<FuncState<CurryState<I, S>>> => {
    if (state[0] === "start") {
      return { action: "input", msg: ["clone"], resume_state: ["inner", ["await_init", msg]] };
    }
    if (state[0] === "inner") {
      const curry_state = state[1];
      if (curry_state[0] === "await_init") {
        const deferred_msg = curry_state[1];
        return { action: "continue", msg, resume_state: ["inner", ["transform_init", ["start"], deferred_msg]] };
      }
      if (curry_state[0] === "transform_init") {
        const init_state = curry_state[1];
        const deferred_msg = curry_state[2];
        const result = stateInit(init_state, msg);
        if (result.action === "result") {
          return { action: "continue", msg: [result.msg, deferred_msg], resume_state: ["inner", ["inner", ["start"]]] };
        }
        return { action: result.action, msg: result.msg, resume_state: ["inner", ["transform_init", result.resume_state, deferred_msg]] };
      }
      if (curry_state[0] === "inner") {
        const inner_state = curry_state[1];
        const result = machine(inner_state, msg);
        if (result.action === "result") {
          const [inner_arg, inner_msg] = result.msg;
          return { action: "result", msg: inner_msg, resume_state: ["inner", ["ready", result.resume_state, inner_arg]] };
        }
        return { action: result.action, msg: result.msg, resume_state: ["inner", ["inner", result.resume_state]] };
      }
      if (curry_state[0] === "ready") {
        const inner_state = curry_state[1];
        const inner_arg = curry_state[2];
        return { action: "continue", msg: [inner_arg, msg], resume_state: ["inner", ["inner", inner_state]] };
      }
      throw Error('Bad state: ' + curry_state[0]);
    }
    throw Error('Bad state: ' + state[0]);
  };
}