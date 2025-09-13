import assert from "assert";

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

export type Startable<T> = T | ["start"];

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
        return { action: result.action, msg: result.msg, resume_state: ["inner", smuggle, result.resume_state] };
      }
      throw Error("Bad state: " + state[0]);
    }
  };
}

export type MatchCases<H> = { [K in keyof H]: Machine<Startable<H[K]>> };
export type MatchState<H> = ["start"] | ["within", keyof H, Startable<H[keyof H]>];

export function match<H>(cases: MatchCases<H>): Machine<MatchState<H>> {
  return (state: MatchState<H>, msg: any): Result<MatchState<H>> => {
    if (state[0] === "start") {
      let [outer_state, selector] = msg;
      return { action: "continue", msg: outer_state, resume_state: ["within", selector, ["start"]] };
    }
    if (state[0] === "within") {
      let selector = state[1];
      let inner_state = state[2];
      if (!(selector in cases)) {
        throw Error("Bad selector: " + String(selector));
      }
      const result = cases[selector](inner_state, msg);
      return { action: result.action, msg: result.msg, resume_state: ["within", selector, result.resume_state] };
    }
    throw Error("Bad state: " + state[0]);
  };
}



type RaiseState = ["start"] | ["await_raise"] | ["end"];
export function raise(state: RaiseState, msg: any): Result<RaiseState> {
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

export const raise2: Combinator<null, RaiseState> = {
  init(_: null): RaiseState {
    return ["start"];
  },
  run(state: RaiseState, msg: any): Result<RaiseState> {
    return raise(state, msg);
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

export type ClosureState<C, S> = ["ready", C, S] | ["inner", S];


export function closure<C, S>(inner: Combinator<null, S>): Combinator<C, ClosureState<C, S>> {
  return {
    init(closure: C): ClosureState<C, S> {
      return ["ready", closure, inner.init(null)];
    },
    run(state: ClosureState<C, S>, msg: any): Result<ClosureState<C, S>> {
      if (state[0] === "ready") {
        const closure = state[1];
        const inner_state = state[2];
        return {
          action: "continue",
          msg: [closure, msg],
          resume_state: ["inner", inner_state],
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
            resume_state: ["ready", new_closure, result.resume_state],
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

export type LoopState<S> = ["start"] | ["inner", Startable<S>] | ["end"];
export function loop<S>(inner: Machine<Startable<S>>): Machine<LoopState<S>> {
  return (state: LoopState<S>, msg: any): Result<LoopState<S>> => {
    if (state[0] === "start") {
      return { action: "continue", msg, resume_state: ["inner", ["start"]] };
    }
    if (state[0] === "inner") {
      const result = inner(state[1], msg);
      if (result.action === "result") {
        const [inner_action, inner_msg] = result.msg;
        if (inner_action === "break") {
          return { action: "result", msg: inner_msg, resume_state: ["end"] };
        }
        if (inner_action === "continue") {
          return { action: "continue", msg: inner_msg, resume_state: ["inner", ["start"]] };
        }
        throw Error('Bad inner action: ' + inner_action);
      }
      return { action: result.action, msg: result.msg, resume_state: ["inner", result.resume_state] };
    }
    throw Error('Bad state: ' + state[0]);
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