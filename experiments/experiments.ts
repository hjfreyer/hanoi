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

type FUNC_ACTION_TYPE = "result" | "return" | "raise";

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
      if (result.action === "result") {
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

export type HandlerResult<S> = Result<S, "resume" | "raise" | "result">

export type Handler<S> = Machine<S, "resume" | "raise" | "result">;


export function call<H, C>(callee: Function<C>, handler: Handler<H>): FuncFragment<CallState<H, C>> {
  return {
    init() { return { kind: "start" } },
    trace(s: CallState<H, C>): string {
      if (s.kind === "start" || s.kind === "ready_to_call") {
        return callee.name + "()";
      }
      if (s.kind === "ready_to_handle") {
        return callee.name + "#handler()";
      }
      if (s.kind === "end") {
        return "end";
      }
      unreachable(s);
    },
    run(state: CallState<H, C>, msg: any): FuncFragmentResult<CallState<H, C>> {
      if (state.kind === "start") {
        const [handler_arg, inner_arg] = msg;
        return { action: "raise", msg: ["continue", inner_arg], resume_state: { kind: "ready_to_call", handler_arg, func_state: callee.init() } };
      }
      if (state.kind === "ready_to_call") {
        const result = callee.run(state.func_state, msg);
        return {
          action: "raise",
          msg: ["continue", [state.handler_arg, [result.action, result.msg]]],
          resume_state: { kind: "ready_to_handle", func_state: result.resume_state, handler_state: handler.init() }
        };
      }
      if (state.kind === "ready_to_handle") {
        const result = handler.run(state.handler_state, msg);
        if (result.action === "resume") {
          const [handler_arg, inner_arg] = result.msg;
          return { action: "raise", msg: ["continue", inner_arg], resume_state: { kind: "ready_to_call", handler_arg, func_state: state.func_state } };
        }
        if (result.action === "raise") {
          return { action: result.action, msg: result.msg, resume_state: { kind: "ready_to_handle", func_state: state.func_state, handler_state: result.resume_state } };
        }
        if (result.action === "result") {
          const [handler_arg, inner_arg] = result.msg;
          return { action: "result", msg: [handler_arg, inner_arg], resume_state: { kind: "end" } };
        }
        throw Error("Bad action: " + result.action);
      }
      throw Error("Bad state: " + state);
    }
  };
}

export function t(f: (msg: any) => any): FuncFragment<null> {
  return {
    init() { return null },
    trace(s: null): string {
      return "t()";
    },
    run(state: null, msg: any): FuncFragmentResult<null> {
      return {
        action: "result",
        msg: f(msg),
        resume_state: state,
      };
    }
  }
}


// export type AndThenState<F, G> = {
//   kind: "start", 
// } | {
//   kind: "first", 
//   state: Startable<F>, 
// } | {
//   kind: "second",
//   state: Startable<G>,
// };

// export function andThen<F, G>(f: FuncFragment<F>, g: FuncFragment<G>): FuncFragment<AndThenState<F, G>> {
//   return (state: AndThenState<F, G>, msg: any): FuncFragmentResult<AndThenState<F, G>> => {
//     if (state.kind === "first") {
//       const result = f(state.state, msg);
//       if (result.action === "result") {
//         return { action: "continue", msg: result.msg, resume_state: ["second", g_state] };
//       }
//       return { action: result.action, msg: result.msg, resume_state: ["first", result.resume_state, g_state] };
//     }
//     if (state.kind === "second") {
//       let g_state = state[1];
//       const result = g(g_state, msg);
//       return { action: result.action, msg: result.msg, resume_state: ["second", result.resume_state] };
//     }
//     throw Error("Bad state: " + state.kind);
//   };
// }


export type SequenceState = [number, any];



export function sequence(...fragments: FuncFragment<any>[]): FuncFragment<SequenceState> {
  return {
    init() { return [0, fragments[0].init()] },
    trace(s: SequenceState): string {
      const [index, inner] = s;
      return "#" + index + fragments[index].trace(inner);
    },
    run(state: SequenceState, msg: any): FuncFragmentResult<SequenceState> {
      const [index, inner] = state;
      const result = fragments[index].run(inner, msg);
      if (result.action === "result") {
        const new_index = index + 1;
        if (new_index < fragments.length) {
          return { action: "raise", msg: ["continue", result.msg], resume_state: [new_index, fragments[new_index].init()] };
        } else {
          return { action: "result", msg: result.msg, resume_state: [-1, null] };
        }
      }
      return { action: result.action, msg: result.msg, resume_state: [index, result.resume_state] };
    }
  };
}


// export type SmuggleState<S> = { kind: "start" } | { kind: "inner", smuggled: unknown, inner: Startable<S> } | { kind: "end" };

// export function smuggle<S>(inner: FuncFragment<S>): FuncFragment<SmuggleState<S>> {
//   return (state: SmuggleState<S>, msg: any): FuncFragmentResult<SmuggleState<S>> => {
//     if (state.kind === "start") {
//       const [smuggled, inner_msg] = msg;
//       return { action: "raise", msg: ["continue", inner_msg], resume_state: { kind: "inner", smuggled, inner: START_STATE } };
//     }
//     if (state.kind === "inner") {
//       const result = inner(state.inner, msg);
//       if (result.action === "result") {
//         return { action: "result", msg: [state.smuggled, result.msg], resume_state: { kind: "end" } };
//       }
//       if (result.action === "return") {
//         return { action: "return", msg: result.msg, resume_state: { kind: "inner", smuggled: state.smuggled, inner: result.resume_state } };
//       }
//       if (result.action === "raise") {
//         return { action: "raise", msg: result.msg, resume_state: { kind: "inner", smuggled: state.smuggled, inner: result.resume_state } };
//       }
//       throw Error("Bad action: " + result.action);
//     }
//     throw Error("Bad state: " + state.kind);
//   }
// }

// export type MatchCases<H> = { [K in keyof H]: FuncFragment<H[K]> };
// export type MatchState<H> = { kind: "start" } | {
//   kind: "within",
//   selector: keyof H,
//   inner: Startable<H[keyof H]>
// };

// export function match<H>(cases: MatchCases<H>): FuncFragment<MatchState<H>> {
//   return (state: MatchState<H>, msg: any): FuncFragmentResult<MatchState<H>> => {
//     if (state.kind === "start") {
//       let [outer_state, selector]: [any, keyof H] = msg;
//       return { action: "raise", msg: ["continue", outer_state], resume_state: { kind: "within", selector, inner: START_STATE } };
//     }
//     if (state.kind === "within") {
//       if (!(state.selector in cases)) {
//         throw Error("Bad selector: " + String(state.selector));
//       }
//       const result = cases[state.selector](state.inner, msg);
//       return { action: result.action, msg: result.msg, resume_state: { kind: "within", selector: state.selector, inner: result.resume_state } };
//     }
//     throw Error("Bad state: " + state);
//   };
// }

type RaiseState = { kind: "start" } | { kind: "await_raise" } | { kind: "end" };

export const raise = {
  init() { return { kind: "start" }; },
  trace(state: RaiseState): string {
    return "raise()";
  },
  run(state: RaiseState, msg: any): FuncFragmentResult<RaiseState> {
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

export function if_then_else<T, F>(then: FuncFragment<T>, els: FuncFragment<F>): FuncFragment<IfThenElseState<T, F>> {
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
    run(state: IfThenElseState<T, F>, msg: any): FuncFragmentResult<IfThenElseState<T, F>> {
      if (state.kind === "start") {
        const [outer_state, cond] = msg;
        if (cond) {
          return {
            action: "raise",
            msg: ["continue", outer_state],
            resume_state: { kind: "then", state: then.init() },
          };
        } else {
          return {
            action: "raise",
            msg: ["continue", outer_state],
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

// export function if_then_else<IT, T, IF, F>(then: Combinator<IT, T>, els: Combinator<IF, F>): Combinator<[IT, IF], IfThenElseState<T, F>> {
//   return {
//     init([arg_t, arg_f]: [IT, IF]): IfThenElseState<T, F> {
//       return ["start", then.init(arg_t), els.init(arg_f)];
//     },
//     run(state: IfThenElseState<T, F>, msg: any): Result<IfThenElseState<T, F>> {
//       return if_then_else_impl(then.run, els.run)(state, msg);
//     }
//   };
// }
// export function if_then_else_null<T, F>(then: Combinator<null, T>, els: Combinator<null, F>): Combinator<null, IfThenElseState<T, F>> {
//   return {
//     init(_: null): IfThenElseState<T, F> {
//       return ["start", then.init(null), els.init(null)];
//     },
//     run(state: IfThenElseState<T, F>, msg: any): Result<IfThenElseState<T, F>> {
//       return if_then_else_impl(then.run, els.run)(state, msg);
//     }
//   };
// }

export type ClosureState<S> = { kind: "start" } | {
  kind: "ready",
  arg: unknown,
} | { kind: "inner", inner: S };


export function closure<S>(inner: Function<S>): Function<ClosureState<S>> {
  return {
    name: "closure(" + inner.name + ")",
    init() { return { kind: "start" }; },
    trace(s: ClosureState<S>): string {
      if (s.kind === "start" || s.kind === "ready") {
        return "closure(" + inner.name + ")";
      }
      if (s.kind === "inner") {
        return inner.trace(s.inner)
      }
      unreachable(s);
    },
    run(state: ClosureState<S>, msg: any): Result<ClosureState<S>, string> {
      if (state.kind === "start") {
        return {
          action: "result",
          msg: null,
          resume_state: { kind: "ready", arg: msg },
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

// export type LoopState<S> = ["inner", S] | ["end"];
// export function loop<S>(inner: Combinator<null, S>): Combinator<null, LoopState<S>> {
//   return {
//     init(_: null): LoopState<S> {
//       return ["inner", inner.init(null)];
//     },
//     run(state: LoopState<S>, msg: any): Result<LoopState<S>> {
//       if (state.kind === "inner") {
//         const result = inner.run(state[1], msg);
//         if (result.action === "result") {
//           const [inner_action, inner_msg] = result.msg;
//           if (inner_action === "break") {
//             return { action: "result", msg: inner_msg, resume_state: ["end"] };
//           }
//           if (inner_action === "continue") {
//             return { action: "continue", msg: inner_msg, resume_state: ["inner", inner.init(null)] };
//           }
//           throw Error('Bad inner action: ' + inner_action);
//         }
//         if (result.action === "return" || result.action === "raise" || result.action === "continue") {
//           return { action: result.action, msg: result.msg, resume_state: ["inner", result.resume_state] };
//         }
//         throw Error('Bad action: ' + result.action);
//       }
//       throw Error('Bad state: ' + state.kind);
//     }
//   };
// }

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