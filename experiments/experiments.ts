import assert from "assert";

export type Result<S> = {
  action: string;
  msg: any;
  resume_state: S;
};

export type Machine<S> = (state: S, msg: any) => Result<S>;

export type HandlerResult<S> = {
  kind: "resume";
  msg: any;
  handler_state: S;
} | {
  kind: "continue";
  action: string;
  msg: any;
  handler_state: S;
};

export type Handler<S> = (handler_name: string, state: S, msg: any) => HandlerResult<S>;

export function transformer<S>(f: (msg: any) => any): Machine<["start"]> {
  return (state, msg) => {
    assert(state[0] === "start", "Bad state: " + state[0]);
    return {
      action: "result",
      msg: f(msg),
      resume_state: state,
    };
  };
}

export type AndThenState<F, G> = ["start"] | ["first", F] | ["second", G];

export type Startable<T> = T | ["start"];

export function andThen<F, G>(f: Machine<Startable<F>>, g: Machine<Startable<G>>): Machine<AndThenState<Startable<F>, Startable<G>>> {
  return (state: AndThenState<Startable<F>, Startable<G>>, msg: any): Result<AndThenState<Startable<F>, Startable<G>>> => {
    if (state[0] === "start") {
      return { action: "continue", msg: msg, resume_state: ["first", ["start"]] };
    }
    if (state[0] === "first") {
      const result = f(state[1], msg);
      if (result.action === "result") {
        return { action: "continue", msg: result.msg, resume_state: ["second", ["start"]] };
      }
      return { action: result.action, msg: result.msg, resume_state: ["first", result.resume_state] };
    }
    if (state[0] === "second") {
      const result = g(state[1], msg);
      return { action: result.action, msg: result.msg, resume_state: ["second", result.resume_state] };
    }
    throw Error("Bad state: " + state[0]);
  };
}

export function sequence(machines: Machine<any>[]): Machine<any> {
  let result = machines[0]; 
  for (const machine of machines.slice(1)) {
    result = andThen(result, machine);
  }
  return result;
}

export type CallState<I, O, H> = ["start"] | ["inner", Startable<I>, O] | ["handler", Startable<I>, Startable<H>] | ["end"];

export function call<I, O, H>(f: Machine<Startable<I>>, handler: Machine<Startable<H>>): Machine<CallState<I, Startable<O>, Startable<H>>> {
  return (state: CallState<I, Startable<O>, Startable<H>>, msg: any): Result<CallState<I, Startable<O>, Startable<H>>> => {
    if (state[0] === "start") {
      let [outer_state, inner_msg] = msg;
      return { action: "continue", msg: inner_msg, resume_state: ["inner", ["start"], outer_state] };
    }
    if (state[0] === "inner") {
      let inner_state = state[1];
      let outer_state = state[2];
      const result = f(inner_state, msg);
      if (result.action === "result") {
        return { action: "result", msg: [outer_state, result.msg], resume_state: ["end"] };
      }
      if (result.action === "continue") {
        return { action: "continue", msg: result.msg, resume_state: ["inner", result.resume_state, outer_state] };
      }
      return { action: "continue", msg: [result.action, outer_state, result.msg], resume_state: ["handler", result.resume_state, ["start"]] };
    }
    if (state[0] === "handler") {
      let inner_state = state[1];
      let handler_state = state[2];
      const handler_result = handler(handler_state, msg);
      if (handler_result.action === "result") {
        let [new_outer_state, new_msg] = handler_result.msg;
        return { action: "continue", msg: new_msg, resume_state: ["inner", inner_state, new_outer_state] };
      }
      return { action: handler_result.action, msg: handler_result.msg, resume_state: ["handler", inner_state, handler_result.resume_state] };
    }
    throw Error("Bad state: " + state[0]);
  };
}

export type SmuggleState<E, S> = ["start"] | ["inner", E, Startable<S>] | ["end"];

export function smuggle<E, S>(inner: Machine<Startable<S>>): Machine<SmuggleState<E, S>> {
  return (state: SmuggleState<E, S>, msg: any): Result<SmuggleState<E, S>> => {
    if (state[0] === "start") {
      let [smuggle, inner_msg] = msg;
      return { action: "continue", msg: inner_msg, resume_state: ["inner", smuggle, ["start"]] };
    }
    if (state[0] === "inner") {
      let smuggle = state[1];
      let inner_state = state[2];
      const result = inner(inner_state, msg);
      if (result.action === "result") {
        return { action: "result", msg: [smuggle, result.msg], resume_state: ["end"] };
      }
      return { action: result.action, msg: result.msg, resume_state: ["inner", smuggle, result.resume_state] };
    }
    throw Error("Bad state: " + state[0]);
  };
}

export type MatchCases<H> = {[K in keyof H]: Machine<Startable<H[K]>>};
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

export type IfThenElseState<T, F> = ["start"] | ["then", Startable<T>] | ["else", Startable<F>];
export function if_then_else<T, F>(then: Machine<Startable<T>>, els: Machine<Startable<F>>): Machine<IfThenElseState<T, F>> {
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

export type ClosureState<C, S> = ["start"] | ["ready", C] | ["inner", Startable<S>];
export function closure<C, S>(inner: Machine<Startable<S>>): Machine<ClosureState<C, S>> {
  return function (state: ClosureState<C, S>, msg: any): Result<ClosureState<C, S>> {
    if (state[0] === "start") {
      const closure = msg;
      return {
        action: "result",
        msg: null,
        resume_state: ["ready", closure],
      };
    }
    if (state[0] === "ready") {
      const closure = state[1];
      return {
        action: "continue",
        msg: [closure, msg],
        resume_state: ["inner", ["start"]],
      }
    }
    if (state[0] === "inner") {
      const inner_state = state[1];
      const result = inner(inner_state, msg);
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
  };
}
