import assert from "assert";


export type Result<S, A> = {
  action: A;
  msg: any;
  resume_state: S;
};

export type Machine<S, A> = {
  init(): S
  run(s: S, msg: any): Result<S, A>
  trace(s: S): string
}

type FUNC_ACTION_TYPE = "result" | "return" | "raise" | "continue";

export type FuncFragmentResult<S> = Result<S, FUNC_ACTION_TYPE>

export type FuncFragment<S> = Machine<S, FUNC_ACTION_TYPE>

// export type Func2State<S> = ["start"] | ["inner", Startable<S>];

// export function func2<S>(inner: FuncFragment<S>): Machine<Func2State<S>> {
//   return (state: Func2State<S>, msg: any): Result<Func2State<S>> => {
//     if (state.kind === "start") {
//       return { action: "continue", msg, resume_state: ["inner", START_STATE] };
//     }
//     if (state.kind === "inner") {
//       const inner_state = state[1];
//       const result = inner(inner_state, msg);
//       if (result.action === "result" || result.action === "continue") {
//         return { action: result.action, msg: result.msg, resume_state: ["inner", result.resume_state] };
//       }
//       if (result.action === "return") {
//         return { action: "result", msg: result.msg, resume_state: ["inner", result.resume_state] };
//       }
//       if (result.action === "raise") {
//         const [action, inner_msg] = result.msg;
//         return { action: action, msg: inner_msg, resume_state: ["inner", result.resume_state] };
//       }
//       throw Error("Bad action: " + result.action);
//     }
//     throw Error("Bad state: " + state.kind);
//   };
// }

// export type SingleStateResult = {
//   action: FUNC_ACTION_TYPE;
//   msg: any;
// }

// export function singleState(func : (msg: any) =>SingleStateResult  ): FuncFragment<START_STATE_TYPE> {
//   return (state: Startable<START_STATE_TYPE>, msg: any) => {
//     const new_result = func(msg);
//     return { action: new_result.action, resume_state: START_STATE, msg: new_result.msg };
//   };
// }

// export function bind(name: string): FuncFragment<START_STATE_TYPE> {
//   return singleState((msg: any) => {
//     const context : FuncFragmentContext = msg;
//     const top = context.stack.pop();
//     return { action: "result", msg: {locals: {name: top, ...context.locals}, stack: context.stack} };
//   });
// }

function unreachable(x: never): never {
  throw Error("Unreachable: " + x);
}

export function makeInner<S>(inner: S): { kind: "inner", inner: S } {
  return { kind: "inner", inner }
}

export type Function<S> = Machine<S, string> & {
  name: string
}

export function func<S>(name: string, inner: FuncFragment<S>): Function<S> {
  return {
    name,
    init() { return inner.init() },
    run(state: S, msg: any): Result<S, string> {
      const result = inner.run(state, msg);
      if (result.action === "result" || result.action === "continue") {
        return { action: result.action, msg: result.msg, resume_state: result.resume_state };
      }
      if (result.action === "return") {
        return { action: "result", msg: result.msg, resume_state: result.resume_state };
      }
      if (result.action === "raise") {
        const [action, inner_msg] = result.msg;
        return { action: action, msg: inner_msg, resume_state: result.resume_state };
      }
      unreachable(result.action);
    },
    trace(s: S): string {
      return inner.trace(s);
    }
  };
}

type CallState<H, C> = {
  kind: "start"
} | {
  kind: "ready_to_call",
  func_state: C,
  handler_arg: unknown,
} | {
  kind: "ready_to_handle",
  func_state: C,
  handler_state: H,
} | {
  kind: "end",
};

export type HandlerResult<S> = Result<S, "abort" | "raise" | "resume" | "continue">

export type Handler<S> = Machine<S, "abort" | "raise" | "resume" | "continue">;

export type CALL_ACTION_TYPE = "raise" | "result" | "continue";

export function call<H, C>(callee: Function<C>, handler: Handler<H>): Machine<CallState<H, C>, CALL_ACTION_TYPE> {
  return {
    init() { return { kind: "start" } },
    trace(s: CallState<H, C>): string {
      if (s.kind === "start" || s.kind === "ready_to_call") {
        return callee.name + "()";
      }
      if (s.kind === "ready_to_handle") {
        return callee.name + "#handler()" + handler.trace(s.handler_state);
      }
      if (s.kind === "end") {
        return "end";
      }
      unreachable(s);
    },
    run(state: CallState<H, C>, msg: any): Result<CallState<H, C>, CALL_ACTION_TYPE> {
      if (state.kind === "start") {
        const [handler_arg, inner_arg] = msg;
        return { action: "continue", msg: inner_arg, resume_state: { kind: "ready_to_call", handler_arg, func_state: callee.init() } };
      }
      if (state.kind === "ready_to_call") {
        const result = callee.run(state.func_state, msg);
        if (result.action === "result") {
          return {
            action: "result",
            msg: [state.handler_arg, result.msg],
            resume_state: { kind: "end" }
          };
        }
        if (result.action === "continue") {
          return { action: "continue", msg: result.msg, resume_state: { kind: "ready_to_call", func_state: result.resume_state, handler_arg: state.handler_arg } };
        }
        return {
          action: "continue",
          msg: [state.handler_arg, [result.action, result.msg]],
          resume_state: { kind: "ready_to_handle", func_state: result.resume_state, handler_state: handler.init() }
        };
      }
      if (state.kind === "ready_to_handle") {
        const result = handler.run(state.handler_state, msg);
        if (result.action === "resume") {
          const [handler_arg, inner_action, inner_arg] = result.msg;
          return { action: "continue", msg: [inner_action, inner_arg], resume_state: { kind: "ready_to_call", handler_arg, func_state: state.func_state } };
        }
        if (result.action === "raise") {
          return { action: "raise", msg: result.msg, resume_state: { kind: "ready_to_handle", func_state: state.func_state, handler_state: result.resume_state } };
        }
        if (result.action === "abort") {
          const [handler_arg, inner_arg] = result.msg;
          return { action: "result", msg: [handler_arg, inner_arg], resume_state: { kind: "end" } };
        }
        if (result.action === "continue") {
          return { action: "continue", msg: result.msg, resume_state: { kind: "ready_to_handle", func_state: state.func_state, handler_state: result.resume_state } };
        }
        unreachable(result.action);
      }
      throw Error("Bad state: " + state);
    }
  };
}

export type DefaultHandlerState = {
  kind: "start"
} | {
  kind: "end"
};

export const defaultHandler: Handler<DefaultHandlerState> = {
  init() { return { kind: "start" } },
  trace(state: DefaultHandlerState): string {
    return "defaultHandler(" + state.kind + ")";
  },
  run(state: DefaultHandlerState, msg: any): HandlerResult<DefaultHandlerState> {
    if (state.kind === "start") {
      const [ctx, [action, args]] = msg;
      if (action === "result") {
        return {
          action: "abort",
          msg: [ctx, args],
          resume_state: { kind: "end" },
        };
      }
      throw Error("Bad action: " + action);
    }
    throw Error("Bad state: " + state.kind);
  }
};

export function callNoRaise<C>(callee: Function<C>) {
  return sequence(
    t((msg: any) => [null, msg]),
    call(callee, defaultHandler),
    t(([_, msg]) => msg),
  );
}


export type SimpleHandlerState<S> = {
  kind: "inner",
  inner: S,
} | {
  kind: "end",
};

export function simpleHandler<S>(inner: Machine<S, "raise" | "result" | "continue">): Handler<SimpleHandlerState<S>> {
  return {
    init() { return { kind: "inner", inner: inner.init() } },
    trace(s: SimpleHandlerState<S>): string {
      if (s.kind === "inner") {
        return inner.trace(s.inner);
      }
      if (s.kind === "end") {
        throw Error("Bad state: " + s.kind);
      }
      unreachable(s);
    },
    run(s: SimpleHandlerState<S>, msg: any): Result<SimpleHandlerState<S>, "abort" | "raise" | "resume" | "continue"> {
      if (s.kind === "inner") {
        const result = inner.run(s.inner, msg);

        if (result.action === "result") {
          const [handler_arg, inner_arg] = result.msg;
          return { action: "resume", msg: [handler_arg, "result", inner_arg], resume_state: { kind: "end" } };
        }
        if (result.action === "raise") {
          return { action: "raise", msg: result.msg, resume_state: { kind: "inner", inner: result.resume_state } };
        }
        if (result.action === "continue") {
          return { action: "continue", msg: result.msg, resume_state: { kind: "inner", inner: result.resume_state } };
        }
        throw Error("Bad action: " + result.action);
      }
      if (s.kind === "end") {
        throw Error("Bad state: " + s.kind);
      }
      unreachable(s);
    }
  };
}

export function t(f: (msg: any) => any): Machine<null, "result"> {
  return {
    init() { return null },
    trace(s: null): string {
      return "t()";
    },
    run(state: null, msg: any): Result<null, "result"> {
      return {
        action: "result",
        msg: f(msg),
        resume_state: state,
      };
    }
  }
}

export type NotResult<T> = T extends "result" ? never : T;
function isNotResult<T>(t: T): t is NotResult<T> {
  return t !== "result";
}


export type AndThenState<AS, BS> = { kind: "a", a: AS } | { kind: "b", b: BS };

export function andThen<AS, AA, BS, BA>(a: Machine<AS, AA | "result">, b: Machine<BS, BA>): Machine<AndThenState<AS, BS>, NotResult<AA> | BA | "continue"> {
  return {
    init() { return { kind: "a", a: a.init() } },
    trace(s: AndThenState<AS, BS>): string {
      if (s.kind === "a") {
        return "#0/" + a.trace(s.a);
      }
      if (s.kind === "b") {
        return "#1/" + b.trace(s.b);
      }
      unreachable(s);
    },
    run(s: AndThenState<AS, BS>, msg: any): Result<AndThenState<AS, BS>, NotResult<AA> | BA | "continue"> {
      if (s.kind === "a") {
        const result = a.run(s.a, msg);
        if (isNotResult(result.action)) {
          return { action: result.action, msg: result.msg, resume_state: { kind: "a", a: result.resume_state } };
        }else {
          return { action: "continue", msg: result.msg, resume_state: { kind: "b", b: b.init() } };
        }
      }
      if (s.kind === "b") {
        const result = b.run(s.b, msg);
        return { action: result.action, msg: result.msg, resume_state: { kind: "b", b: result.resume_state } };
      }
      unreachable(s);
    }
  };
}

export type SequenceState = [number, any];

export function sequence<A>(...fragments: Machine<any, A>[]): Machine<SequenceState, A | "continue"> {
  return {
    init() { return [0, fragments[0].init()] },
    trace(s: SequenceState): string {
      const [index, inner] = s;
      return "#" + index + fragments[index].trace(inner);
    },
    run(state: SequenceState, msg: any): Result<SequenceState, A | "continue"> {
      const [index, inner] = state;
      const result = fragments[index].run(inner, msg);
      if (result.action === "result") {
        const new_index = index + 1;
        if (new_index < fragments.length) {
          return { action: "continue", msg: result.msg, resume_state: [new_index, fragments[new_index].init()] };
        }
      }
      return { action: result.action, msg: result.msg, resume_state: [index, result.resume_state] };
    }
  };
}

export type SmuggleState<S> = { kind: "start" } | { kind: "inner", smuggled: unknown, inner: S } | { kind: "end" };

export function smuggle<S, A>(inner: Machine<S, A>): Machine<SmuggleState<S>, A | "raise" | "result" | "continue"> {
  return {
    init() { return { kind: "start" } },
    trace(state: SmuggleState<S>): string {
      if (state.kind === "start") {
        return "smuggle()";
      }
      if (state.kind === "inner") {
        return inner.trace(state.inner);
      }
      if (state.kind === "end") {
        throw Error("Bad state: " + state.kind);
      }
      unreachable(state);
    },
    run(state: SmuggleState<S>, msg: any): Result<SmuggleState<S>, A | "raise" | "result" | "continue"> {
      if (state.kind === "start") {
        const [smuggled, inner_msg] = msg;
        return { action: "continue", msg: inner_msg, resume_state: { kind: "inner", smuggled, inner: inner.init() } };
      }
      if (state.kind === "inner") {
        const result = inner.run(state.inner, msg);
        if (result.action === "result") {
          return { action: "result", msg: [state.smuggled, result.msg], resume_state: { kind: "end" } };
        } else {
          return { action: result.action, msg: result.msg, resume_state: { kind: "inner", smuggled: state.smuggled, inner: result.resume_state } };
        }
      }
      if (state.kind === "end") {
        throw Error("Bad state: " + state.kind);
      }
      unreachable(state);
    }
  };
}

export type MatchCases<H extends Record<string, { S: any, A: any }>> = { [K in keyof H]: Machine<H[K]["S"], H[K]["A"]> };

export type MatchState<H extends Record<string, { S: any, A: any }>> = {
  kind: "start"
} | {
  kind: "within",
  selector: keyof H,
  inner: H[keyof H]["S"],
};

export function match<H extends Record<string, { S: any, A: any }>>(cases: MatchCases<H>): Machine<MatchState<H>, H[keyof H]["A"] | "raise" | "continue"> {
  return {
    init() { return { kind: "start" }; },
    trace(state: MatchState<H>): string {
      if (state.kind === "start") {
        return "match()";
      }
      if (state.kind === "within") {
        return "match(" + String(state.selector) + ")" + cases[state.selector].trace(state.inner);
      }
      unreachable(state);
    },
    run(state: MatchState<H>, msg: any): Result<MatchState<H>, H[keyof H]["A"] | "raise" | "continue"> {
      if (state.kind === "start") {
        let [outer_state, selector]: [any, keyof H] = msg;
        if (!(selector in cases)) {
          throw Error("Bad selector: " + String(selector));
        }
        return { action: "continue", msg: outer_state, resume_state: { kind: "within", selector, inner: cases[selector].init() } };
      }
      if (state.kind === "within") {
        if (!(state.selector in cases)) {
          throw Error("Bad selector: " + String(state.selector));
        }
        const result = cases[state.selector].run(state.inner, msg);
        return { action: result.action, msg: result.msg, resume_state: { kind: "within", selector: state.selector, inner: result.resume_state } };
      }
      throw Error("Bad state: " + state);
    }
  };
}

type RaiseState = { kind: "start" } | { kind: "await_raise" } | { kind: "end" };

export const raise: Machine<RaiseState, "raise" | "result"> = {
  init() { return { kind: "start" }; },
  trace(state: RaiseState): string {
    return "raise()";
  },
  run(state: RaiseState, msg: any): Result<RaiseState, "raise" | "result"> {
    if (state.kind === "start") {
      return {
        action: "raise",
        msg: msg,
        resume_state: { kind: "await_raise" },
      };
    }
    if (state.kind === "await_raise") {
      const [action, inner_msg] = msg;
      if (action !== "result") {
        throw Error("Bad action: " + action);
      }
      return {
        action: "result",
        msg: inner_msg,
        resume_state: { kind: "end" },
      };
    }
    throw Error('Bad state: ' + state.kind);
  }
};


type RaiseRaiseState<H> = {
  kind: "start"
} | {
  kind: "ready_to_raise",
  handler_arg: unknown
} | {
  kind: "process_response",
  handler_arg: unknown
} | {
  kind: "ready_to_handle",
  handler_arg: unknown
} | { kind: "handling", handler_state: H } | { kind: "end" };

export function raiseRaise<H>(action: string, handler: Handler<H>): Machine<RaiseRaiseState<H>, "raise" | "result" | "continue"> {
  return {
    init() { return { kind: "start" }; },
    trace(state: RaiseRaiseState<H>): string {
      if (state.kind === "start") {
        return "raise(" + action + ")";
      }
      if (state.kind === "ready_to_raise") {
        return "raise(" + action + ")";
      }
      if (state.kind === "process_response") {
        return "raise(" + action + ").process_response";
      }
      if (state.kind === "ready_to_handle") {
        return "raise(" + action + ").handler";
      }
      if (state.kind === "handling") {
        return "raise(" + action + ").handler" + handler.trace(state.handler_state);
      }
      if (state.kind === "end") {
        throw Error("Bad state: " + state.kind);
      }
      unreachable(state);
    },
    run(state: RaiseRaiseState<H>, msg: any): Result<RaiseRaiseState<H>, "raise" | "result" | "continue"> {
      if (state.kind === "start") {
        const [handler_arg, inner_msg] = msg;
        return {
          action: "continue",
          msg: inner_msg,
          resume_state: { kind: "ready_to_raise", handler_arg },
        };
      }
      if (state.kind === "ready_to_raise") {
        return { action: "raise", msg: [action, msg], resume_state: { kind: "process_response", handler_arg: state.handler_arg } };
      }
      if (state.kind === "process_response") {
        const [action, inner_msg] = msg;
        if (action === "result") {
          return { action: "result", msg: [state.handler_arg, inner_msg], resume_state: { kind: "end" } };
        } else {
          return { action: "continue", msg, resume_state: { kind: "ready_to_handle", handler_arg: state.handler_arg } };
        }
      }
      if (state.kind === "ready_to_handle") {
        return { action: "continue", msg: [state.handler_arg, msg], resume_state: { kind: "handling", handler_state: handler.init() } };
      }
      if (state.kind === "handling") {
        const result = handler.run(state.handler_state, msg);
        if (result.action === "resume") {
          const [handler_arg, inner_action, inner_arg] = result.msg;
          return { action: "continue", msg: [inner_action, inner_arg], resume_state: { kind: "ready_to_raise", handler_arg } };
        }
        if (result.action === "raise") {
          return { action: "raise", msg: result.msg, resume_state: { kind: "handling", handler_state: result.resume_state } };
        }
        if (result.action === "abort") {
          const [handler_arg, inner_arg] = result.msg;
          return { action: "result", msg: [handler_arg, inner_arg], resume_state: { kind: "end" } };
        }
        if (result.action === "continue") {
          return { action: "continue", msg: result.msg, resume_state: { kind: "handling", handler_state: result.resume_state } };
        }
        unreachable(result.action);
      }
      throw Error('Bad state: ' + state.kind);
    }
  };
}
// type RetState = ["start"] | ["await_return"] | ["end"];

// export const ret: Combinator<null, RetState> = {
//   init(_: null): RetState {
//     return ["start"];
//   },
//   run(state: RetState, msg: any): Result<RetState> {
//     if (state.kind === "start") {
//       return {
//         action: "return",
//         msg: msg,
//         resume_state: ["await_return"],
//       };
//     }
//     if (state.kind === "await_return") {
//       return {
//         action: "result",
//         msg: msg,
//         resume_state: ["end"],
//       };
//     }
//     throw Error('Bad state: ' + state.kind);
//   }
// };

export type IfThenElseState<T, F> = { kind: "start" } | { kind: "then", state: T } | { kind: "else", state: F };

export function if_then_else<A, T, F>(then: Machine<T, A>, els: Machine<F, A>): Machine<IfThenElseState<T, F>, A | "continue"> {
  return {
    init() { return { kind: "start" }; },
    trace(state: IfThenElseState<T, F>): string {
      if (state.kind === "start") {
        return "if(cond)";
      }
      if (state.kind === "then") {
        return "if(true)" + then.trace(state.state);
      }
      if (state.kind === "else") {
        return "if(false)" + els.trace(state.state);
      }
      unreachable(state);
    },
    run(state: IfThenElseState<T, F>, msg: any): Result<IfThenElseState<T, F>, A | "continue"> {
      if (state.kind === "start") {
        const [outer_state, cond] = msg;
        if (cond) {
          return {
            action: "continue",
            msg: outer_state,
            resume_state: { kind: "then", state: then.init() },
          };
        } else {
          return {
            action: "continue",
            msg: outer_state,
            resume_state: { kind: "else", state: els.init() },
          };
        }
      }
      if (state.kind === "then") {
        const result = then.run(state.state, msg);
        return {
          action: result.action,
          msg: result.msg,
          resume_state: { kind: "then", state: result.resume_state },
        }
      }
      if (state.kind === "else") {
        const result = els.run(state.state, msg);
        return {
          action: result.action,
          msg: result.msg,
          resume_state: { kind: "else", state: result.resume_state },
        };
      }
      unreachable(state);
    }
  };
}

export type ClosureState<C, S> = {
  kind: "in_constructor",
  constructor_state: C,
} | {
  kind: "ready",
  arg: unknown,
} | { kind: "inner", inner: S };


export function closure<C, S>(constructor: Function<C>, inner: Function<S>): Function<ClosureState<C, S>> {
  return {
    name: "closure(" + inner.name + ")",
    init() { return { kind: "in_constructor", constructor_state: constructor.init() }; },
    trace(s: ClosureState<C, S>): string {
      if (s.kind === "ready") {
        return "closure(" + inner.name + ")";
      }
      if (s.kind === "in_constructor") {
        return "closure(" + inner.name + ").constructor(" + constructor.name + ")" + constructor.trace(s.constructor_state);
      }
      if (s.kind === "inner") {
        return inner.trace(s.inner)
      }
      unreachable(s);
    },
    run(state: ClosureState<C, S>, msg: any): Result<ClosureState<C, S>, string> {
      if (state.kind === "in_constructor") {
        const result = constructor.run(state.constructor_state, msg);
        if (result.action === "result") {
          return {
            action: "result",
            msg: null,
            resume_state: { kind: "ready", arg: result.msg },
          };
        } else {
          return {
            action: result.action,
            msg: result.msg,
            resume_state: { kind: "in_constructor", constructor_state: result.resume_state },
          }
        }
      }
      if (state.kind === "ready") {
        return {
          action: "continue",
          msg: [state.arg, msg],
          resume_state: { kind: "inner", inner: inner.init() },
        }
      }
      if (state.kind === "inner") {
        const result = inner.run(state.inner, msg);
        if (result.action === "result") {
          const [new_closure, new_output] = result.msg;
          return {
            action: "result",
            msg: new_output,
            resume_state: { kind: "ready", arg: new_closure },
          };
        }
        return {
          action: result.action,
          msg: result.msg,
          resume_state: { kind: "inner", inner: result.resume_state },
        };
      }
      throw Error('Bad state: ' + state);
    }
  }
};
// export function withInit<I, S>(value: I, inner: Combinator<I, S>): Combinator<null, S> {
//   return {
//     init(arg: null): S {
//       return inner.init(value);
//     },
//     run(state: S, msg: any): Result<S> {
//       return inner.run(state, msg);
//     }
//   };
// }

export type LoopState<S> = { kind: "inner", state: S } | { kind: "end" };
export function loop<S>(inner: Machine<S, "break" | "continue" | "next" | "raise">): Machine<LoopState<S>, "result" | "continue" | "raise"> {
  return {
    init(): LoopState<S> {
      return { kind: "inner", state: inner.init() };
    },
    trace(state: LoopState<S>): string {
      if (state.kind === "inner") {
        return "loop(" + inner.trace(state.state) + ")";
      }
      if (state.kind === "end") {
        return "loop(end)";
      }
      unreachable(state);
    },
    run(state: LoopState<S>, msg: any): Result<LoopState<S>, "result" | "continue" | "raise"> {
      if (state.kind === "inner") {
        const result = inner.run(state.state, msg);

        if (result.action === "next") {
          return { action: "continue", msg: result.msg, resume_state: { kind: "inner", state: inner.init() } };
        }
        if (result.action === "break") {
          return { action: "result", msg: result.msg, resume_state: { kind: "end" } };
        }
        if (result.action === "continue") {
          return { action: "continue", msg: result.msg, resume_state: { kind: "inner", state: result.resume_state } };
        }
        if (result.action === "raise") {
          return { action: "raise", msg: result.msg, resume_state: { kind: "inner", state: result.resume_state } };
        }
        unreachable(result.action);
      }
      throw Error('Bad state: ' + state.kind);
    }
  };
}

export const brk: Machine<null, "break"> = {
  init() { return null },
  trace(state: null): string {
    return "brk";
  },
  run(state: null, msg: any): Result<null, "break"> {
    return { action: "break", msg, resume_state: null };
  }
};


export const next: Machine<null, "next"> = {
  init() { return null },
  trace(state: null): string {
    return "next";
  },
  run(state: null, msg: any): Result<null, "next"> {
    return { action: "next", msg, resume_state: null };
  }
};
// export type HandleState<H, I> = ["inner", H, I] | ["handler", H, I] | ["end"];

// export function handle<HI, H, II, I>(action: string, handler: Combinator<HI, H>, inner: Combinator<II, I>): Combinator<[HI, II], HandleState<H, I>> {
//   return {
//     init(arg: [HI, II]) {
//       return ["inner", handler.init(arg[0]), inner.init(arg[1])];
//     },
//     run(state: HandleState<H, I>, msg: any): Result<HandleState<H, I>> {
//       if (state.kind === "inner") {
//         const handler_state = state[1];
//         const inner_state = state[2];
//         const result = inner.run(inner_state, msg);
//         if (result.action === action) {
//           return { action: "continue", msg: result.msg, resume_state: ["handler", handler_state, result.resume_state] };
//         }
//         return { action: result.action, msg: result.msg, resume_state: ["inner", handler_state, result.resume_state] };
//       }
//       if (state.kind === "handler") {
//         const handler_state = state[1];
//         const inner_state = state[2];
//         const result = handler.run(handler_state, msg);
//         if (result.action === "result") {
//           return { action: "continue", msg: result.msg, resume_state: ["inner", result.resume_state, inner_state] };
//         }
//         return { action: result.action, msg: result.msg, resume_state: ["handler", result.resume_state, inner_state] };
//       }
//       throw Error('Bad state: ' + state.kind);
//     }
//   };
// }

// export type ConstructState<S> = ["start"] | ["inner", S];

// export function construct<S>(inner: Combinator<unknown, S>): Combinator<null, ConstructState<S>> {
//   return {
//     init(_: null): ConstructState<S> {
//       return ["start"];
//     },
//     run(state: ConstructState<S>, msg: any): Result<ConstructState<S>> {
//       if (state.kind === "start") {
//         const [state, inner_msg] = msg;
//         return { action: "continue", msg: inner_msg, resume_state: ["inner", inner.init(state)] };
//       }
//       if (state.kind === "inner") {
//         const inner_state = state[1];
//         const result = inner.run(inner_state, msg);
//         return { action: result.action, msg: result.msg, resume_state: ["inner", result.resume_state] };
//       }
//       throw Error('Bad state: ' + state.kind);
//     }
//   };
// }

// type CurryState<I, S> = ["await_init", unknown] | ["transform_init", FuncState<I>, unknown] | ["inner", FuncState<S>] | ["ready", FuncState<S>, unknown];

// export function curryState<I, S>(stateInit: Machine<FuncState<I>>, machine: Machine<FuncState<S>>): Machine<FuncState<CurryState<I, S>>> {
//   return (state: FuncState<CurryState<I, S>>, msg: any): Result<FuncState<CurryState<I, S>>> => {
//     if (state.kind === "start") {
//       return { action: "input", msg: ["clone"], resume_state: ["inner", ["await_init", msg]] };
//     }
//     if (state.kind === "inner") {
//       const curry_state = state[1];
//       if (curry_state.kind === "await_init") {
//         const deferred_msg = curry_state[1];
//         return { action: "continue", msg, resume_state: ["inner", ["transform_init", ["start"], deferred_msg]] };
//       }
//       if (curry_state.kind === "transform_init") {
//         const init_state = curry_state[1];
//         const deferred_msg = curry_state[2];
//         const result = stateInit(init_state, msg);
//         if (result.action === "result") {
//           return { action: "continue", msg: [result.msg, deferred_msg], resume_state: ["inner", ["inner", ["start"]]] };
//         }
//         return { action: result.action, msg: result.msg, resume_state: ["inner", ["transform_init", result.resume_state, deferred_msg]] };
//       }
//       if (curry_state.kind === "inner") {
//         const inner_state = curry_state[1];
//         const result = machine(inner_state, msg);
//         if (result.action === "result") {
//           const [inner_arg, inner_msg] = result.msg;
//           return { action: "result", msg: inner_msg, resume_state: ["inner", ["ready", result.resume_state, inner_arg]] };
//         }
//         return { action: result.action, msg: result.msg, resume_state: ["inner", ["inner", result.resume_state]] };
//       }
//       if (curry_state.kind === "ready") {
//         const inner_state = curry_state[1];
//         const inner_arg = curry_state[2];
//         return { action: "continue", msg: [inner_arg, msg], resume_state: ["inner", ["inner", inner_state]] };
//       }
//       throw Error('Bad state: ' + curry_state.kind);
//     }
//     throw Error('Bad state: ' + state.kind);
//   };
// }