import assert from "assert";

// reactor_send(self, msg, )


export type Action<A, M> = {action: A, msg: M};

export type Machine<S, I extends Action<any, any>, O extends Action<any, any>> = {
  init(): S;
  trace(s: S): string;
  run(state: S, input: I): [S, O];
}

export function t<I, O>(f: (msg: I) => O): Machine<null, {action: "input", msg: I}, {action: "result", msg: O}> {
  return {
    init() { return null },
    trace(s: null): string {
      return "t()";
    },
    run(state: null, input: {action: "input", msg: I}): [null, {action: "result", msg: O}] {
      return [null, {action: "result", msg: f(input.msg) }];
    },
  };
}

type NoInput<T> = T extends {action: "input"} ? never : T;
type NoResult<T> = T extends {action: "result"} ? never : T;


function isNoResult<T extends Action<any, any>>(t: T ): t is NoResult<T> {
  return t.action !== "result";
}

export type AndThenState<AS, BS> = { kind: "a", a: AS } | { kind: "b", b: BS };

export type AndThenInput<AI, BI, T> = AI | NoInput<BI> | {action: "input", msg: T}
export type AndThenOutput<AO, BO, T> = NoResult<AO> | BO;

export function andThen<AS, AI extends Action<any, any>, AO extends Action<any, any>, BS, BI extends Action<any, any>, BO extends Action<any, any>, T>(
    a: Machine<AS, AI, AO | {action: "result", msg: T}>, b: Machine<BS, BI | {action: "input", msg: T}, BO>): Machine<AndThenState<AS, BS>, AndThenInput<AI, BI, T>, AndThenOutput<AO, BO, T>> {
  return {
    init() { return { kind: "a", a: a.init() } },
    trace(s: AndThenState<AS, BS>): string {
      if (s.kind === "a") {
        return "a#" + a.trace(s.a);
      }
      if (s.kind === "b") {
        return "b#" + b.trace(s.b);
      }
      unreachable(s);
    },
    run(state: AndThenState<AS, BS>, input: AndThenInput<AI, BI, T>): [AndThenState<AS, BS>, AndThenOutput<AO, BO, T>] {
      function run_a(state: AS, input: AI): [AndThenState<AS, BS>, AndThenOutput<AO, BO, T>] {
        const [new_state, result] = a.run(state, input);
        if (isNoResult(result)) {
          return [{kind: "a", a: new_state}, result];
        } else {
          return run_b(b.init(), result.msg);
        }
      }

      function run_b(state: BS, input: BI|{action: "input", msg: T}): [AndThenState<AS, BS>, AndThenOutput<AO, BO, T>] {
        const [new_state, result] = b.run(state, input);
        return [{kind: "b", b: new_state}, result];
      }

      if (state.kind === "a") {
        return run_a(state.a, input as AI);
      }
      if (state.kind === "b") {
        return run_b(state.b, input as BI);
      }
      unreachable(state);
    },
  };
}


export type FuncFragmentInput<I> = Action<"input", I> | Action<"resume", Action<any, any>>;
export type FuncFragmentOutput<O> = Action<"result" | "return", O> | Action<"raise", Action<any, any>>;

export type FuncFragment<S, I, O> = Machine<S, FuncFragmentInput<I>, FuncFragmentOutput<O>>

function unreachable(x: never): never {
  throw Error("Unreachable: " + x);
}

export function makeInner<S>(inner: S): { kind: "inner", inner: S } {
  return { kind: "inner", inner }
}

export type Function<S> = Machine<S, Action<any, any>, Action<any, any>> & {
  name: string
}

export function func<S, I, O>(name: string, inner: FuncFragment<S, I, O>): Function<S> {
  return {
    name,
    init() { return inner.init() },
    run(state: S, msg: any): [S, Action<"result" | "return" | "continue", any>] {
      const [new_state, result] = inner.run(state, msg);
      if (result.action === "result" || result.action === "return") {
        return [new_state, { action: "result", msg: result.msg }];
      }
      if (result.action === "raise") {
        return [new_state, result.msg];
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

// export type CallInput<H, C> = Action<"input", [any, any]>;

// export type Handler<S> = Machine<S, Action<any, any>, Action<"abort" | "raise" | "resume" | "continue", any>>;

// export type CALL_ACTION_TYPE = "raise" | "result" | "continue";

// export function call<H, C>(callee: Function<C>, handler: Handler<H>): Machine<CallState<H, C>, CallInput<H, C>, Action<CALL_ACTION_TYPE, any>> {
//   return {
//     init() { return { kind: "start" } },
//     trace(s: CallState<H, C>): string {
//       if (s.kind === "start" || s.kind === "ready_to_call") {
//         return callee.name + "()";
//       }
//       if (s.kind === "ready_to_handle") {
//         return callee.name + "#handler()" + handler.trace(s.handler_state);
//       }
//       if (s.kind === "end") {
//         return "end";
//       }
//       unreachable(s);
//     },
//     run(state: CallState<H, C>, action: CallInput<H, C>): [CallState<H, C>, Action<CALL_ACTION_TYPE, any>] {
//       if (state.kind === "start") {
//         if (action.action !== "input") {
//           throw Error("Bad message: " + action);
//         }
//         const [handler_arg, inner_arg] = action.msg;
//         return [{ kind: "ready_to_call", handler_arg, func_state: callee.init() }, { action: "continue", msg: {action: "input", msg: inner_arg } }];
//       }
//       if (state.kind === "ready_to_call") {
//         const [new_state, result] = callee.run(state.func_state, action);
//         if (result.action === "result") {
//           return [{ kind: "end" }, { action: "result", msg: [state.handler_arg, result.msg ] }];
//         }
//         if (result.action === "continue") {
//           return [{ kind: "ready_to_call", func_state: new_state, handler_arg: state.handler_arg }, result.action];
//         }
//         return [{ kind: "ready_to_handle", func_state: new_state, handler_state: handler.init() }, { action: "continue", msg: {action: result.action, msg: [state.handler_arg, result.msg] } }];
//       }
//       if (state.kind === "ready_to_handle") {
//         const [new_handler_state, result] = handler.run(state.handler_state, action);
//         if (result.action === "resume") {
//           const [handler_arg, inner_action] = result.msg;
//           return [{ kind: "ready_to_call", handler_arg, func_state: state.func_state }, { action: "continue", msg: inner_action }];
//         }
//         if (result.action === "raise") {
//           return [{ kind: "ready_to_handle", func_state: state.func_state, handler_state: new_handler_state }, { action: "raise", msg: result.msg }];
//         }
//         if (result.action === "abort") {
//           const [handler_arg, inner_arg] = result.msg;
//           return [{ kind: "end" }, { action: "result", msg: [handler_arg, inner_arg] }];
//         }
//         if (result.action === "continue") {
//           return [{ kind: "ready_to_handle", func_state: state.func_state, handler_state: new_handler_state }, { action: "continue", msg: result.msg }];
//         }
//         unreachable(result.action);
//       }
//       throw Error("Bad state: " + state);
//     }
//   };
// }

// // export type DefaultHandlerState = {
// //   kind: "start"
// // } | {
// //   kind: "end"
// // };

// // export const defaultHandler: Handler<DefaultHandlerState> = {
// //   init() { return { kind: "start" } },
// //   trace(state: DefaultHandlerState): string {
// //     return "defaultHandler(" + state.kind + ")";
// //   },
// //   run(state: DefaultHandlerState, msg: any): HandlerResult<DefaultHandlerState> {
// //     if (state.kind === "start") {
// //       const [ctx, [action, args]] = msg;
// //       if (action === "result") {
// //         return {
// //           action: "abort",
// //           msg: [ctx, args],
// //           resume_state: { kind: "end" },
// //         };
// //       }
// //       throw Error("Bad action: " + action);
// //     }
// //     throw Error("Bad state: " + state.kind);
// //   }
// // };

// // export function callNoRaise<C>(callee: Function<C>) {
// //   return sequence(
// //     t((msg: any) => [null, msg]),
// //     call(callee, defaultHandler),
// //     t(([_, msg]) => msg),
// //   );
// // }


// // export type SimpleHandlerState<S> = {
// //   kind: "inner",
// //   inner: S,
// // } | {
// //   kind: "end",
// // };

// // export function simpleHandler<S>(inner: Machine<S, "raise" | "result" | "continue">): Handler<SimpleHandlerState<S>> {
// //   return {
// //     init() { return { kind: "inner", inner: inner.init() } },
// //     trace(s: SimpleHandlerState<S>): string {
// //       if (s.kind === "inner") {
// //         return inner.trace(s.inner);
// //       }
// //       if (s.kind === "end") {
// //         throw Error("Bad state: " + s.kind);
// //       }
// //       unreachable(s);
// //     },
// //     run(s: SimpleHandlerState<S>, msg: any): Result<SimpleHandlerState<S>, "abort" | "raise" | "resume" | "continue"> {
// //       if (s.kind === "inner") {
// //         const result = inner.run(s.inner, msg);

// //         if (result.action === "result") {
// //           const [handler_arg, inner_arg] = result.msg;
// //           return { action: "resume", msg: [handler_arg, "result", inner_arg], resume_state: { kind: "end" } };
// //         }
// //         if (result.action === "raise") {
// //           return { action: "raise", msg: result.msg, resume_state: { kind: "inner", inner: result.resume_state } };
// //         }
// //         if (result.action === "continue") {
// //           return { action: "continue", msg: result.msg, resume_state: { kind: "inner", inner: result.resume_state } };
// //         }
// //         throw Error("Bad action: " + result.action);
// //       }
// //       if (s.kind === "end") {
// //         throw Error("Bad state: " + s.kind);
// //       }
// //       unreachable(s);
// //     }
// //   };
// // }

// export type NotResult<T> = T extends "result" ? never : T;
// function isNotResult<T>(t: T): t is NotResult<T> {
//   return t !== "result";
// }

// export type SequenceState = [number, any];

// export function sequence<A>(...fragments: Machine<any, any, Action<A, any>>[]): Machine<SequenceState, any, Action<A | "continue", any>> {
//   return {
//     init() { return [0, fragments[0].init()] },
//     trace(s: SequenceState): string {
//       const [index, inner] = s;
//       return "#" + index + fragments[index].trace(inner);
//     },
//     run(state: SequenceState, msg: any): [SequenceState, Action<A | "continue", any>] {
//       const [index, inner] = state;
//       const [new_state, result] = fragments[index].run(inner, msg);
//       if (result.action === "result") {
//         const new_index = index + 1;
//         if (new_index < fragments.length) {
//           return [[new_index, fragments[new_index].init()], { action: "continue", msg: {action: "input", msg: result.msg } }];
//         }
//       }
//       return [ [index, new_state], { action: result.action, msg: result.msg}];
//     }
//   };
// }

// export type SmuggleState<S> = { kind: "start" } | { kind: "inner", smuggled: unknown, inner: S } | { kind: "end" };

// export function smuggle<S, A>(inner: Machine<S, any, Action<A, any>>): Machine<SmuggleState<S>, any, Action<A | "raise" | "result" | "continue", any>> {
//   return {
//     init() { return { kind: "start" } },
//     trace(state: SmuggleState<S>): string {
//       if (state.kind === "start") {
//         return "smuggle()";
//       }
//       if (state.kind === "inner") {
//         return inner.trace(state.inner);
//       }
//       if (state.kind === "end") {
//         throw Error("Bad state: " + state.kind);
//       }
//       unreachable(state);
//     },
//     run(state: SmuggleState<S>, action: any): [SmuggleState<S>, Action<A | "raise" | "result" | "continue", any>] {
//       if (state.kind === "start") {
//         if (action.action !== "input") {
//           throw Error("Bad message: " + action);
//         }
//         const [smuggled, inner_msg] = action.msg;
//         return [ { kind: "inner", smuggled, inner: inner.init() } , { action: "continue", msg: {action: "input", msg: inner_msg} }];
//       }
//       if (state.kind === "inner") {
//         const [new_state, result] = inner.run(state.inner, action);
//         if (result.action === "result") {
//           return [{ kind: "end" }, { action: "result", msg: [state.smuggled, result.msg] }];
//         } else {
//           return [{ kind: "inner", smuggled: state.smuggled, inner: new_state }, { action: result.action, msg: result.msg }];
//         }
//       }
//       if (state.kind === "end") {
//         throw Error("Bad state: " + state.kind);
//       }
//       unreachable(state);
//     }
//   };
// }

// export type MatchCases<H extends Record<string, { S: any, I: any, O: any }>> = { [K in keyof H]: Machine<H[K]["S"], H[K]["I"], H[K]["O"]> };

// export type MatchState<H extends Record<string, { S: any, I: any, O: any }>> = {
//   kind: "start"
// } | {
//   kind: "within",
//   selector: keyof H,
//   inner: H[keyof H]["S"],
// };

// export function match<H extends Record<string, { S: any, I: any, O: any }>>(cases: MatchCases<H>): Machine<MatchState<H>, Action<keyof H, H[keyof H]["I"]> , H[keyof H]["O"] | {action: "raise" | "continue", msg: any}> {
//   return {
//     init() { return { kind: "start" }; },
//     trace(state: MatchState<H>): string {
//       if (state.kind === "start") {
//         return "match()";
//       }
//       if (state.kind === "within") {
//         return "match(" + String(state.selector) + ")" + cases[state.selector].trace(state.inner);
//       }
//       unreachable(state);
//     },
//     run(state: MatchState<H>, action: Action<keyof H, H[keyof H]["I"]>): [MatchState<H>, H[keyof H]["O"]| {action: "raise" | "continue", msg: any}] {
//       if (state.kind === "start") {
//         if (!(action.action in cases)) {
//           throw Error("Bad action: " + String(action.action));
//         }
//         return [{ kind: "within", selector: action.action, inner: cases[action.action].init() }, { action: "continue", msg: {action: "input", msg: action.msg} }];
//       }
//       if (state.kind === "within") {
//         if (!(state.selector in cases)) {
//           throw Error("Bad selector: " + String(state.selector));
//         }
//         const [new_state, result] = cases[state.selector].run(state.inner, action);
//         return [{ kind: "within", selector: state.selector, inner: new_state }, result];
//       }
//       throw Error("Bad state: " + state);
//     }
//   };
// }

// type RaiseState = { kind: "start" } | { kind: "await_raise" } | { kind: "end" };

// export const raise: Machine<RaiseState, any, Action<"raise" | "result", any>> = {
//   init() { return { kind: "start" }; },
//   trace(state: RaiseState): string {
//     return "raise()";
//   },
//   run(state: RaiseState, action: any): [RaiseState, Action<"raise" | "result", any>] {
//     if (state.kind === "start") {
//       if (action.action !== "input") {
//         throw Error("Bad message: " + action);
//       }
//       return [{ kind: "await_raise" }, { action: "raise", msg: action.msg }];
//     }
//     if (state.kind === "await_raise") {
//       if (action.action !== "result") {
//         throw Error("Bad action: " + action.action);
//       }
//       return [{ kind: "end" }, action];
//     }
//     throw Error('Bad state: ' + state.kind);
//   }
// };


// type RaiseRaiseState<H> = {
//   kind: "start"
// } | {
//   kind: "ready_to_raise",
//   handler_arg: unknown
// } | {
//   kind: "process_response",
//   handler_arg: unknown
// } | {
//   kind: "ready_to_handle",
//   handler_arg: unknown
// } | { kind: "handling", handler_state: H } | { kind: "end" };

// export function raiseRaise<H>(action: string, handler: Handler<H>): Machine<RaiseRaiseState<H>, "raise" | "result" | "continue"> {
//   return {
//     init() { return { kind: "start" }; },
//     trace(state: RaiseRaiseState<H>): string {
//       if (state.kind === "start") {
//         return "raise(" + action + ")";
//       }
//       if (state.kind === "ready_to_raise") {
//         return "raise(" + action + ")";
//       }
//       if (state.kind === "process_response") {
//         return "raise(" + action + ").process_response";
//       }
//       if (state.kind === "ready_to_handle") {
//         return "raise(" + action + ").handler";
//       }
//       if (state.kind === "handling") {
//         return "raise(" + action + ").handler" + handler.trace(state.handler_state);
//       }
//       if (state.kind === "end") {
//         throw Error("Bad state: " + state.kind);
//       }
//       unreachable(state);
//     },
//     run(state: RaiseRaiseState<H>, action: Action<any, any>): [RaiseRaiseState<H>, Action<"raise" | "result" | "continue", any>] {
//       if (state.kind === "start") {
//         if (action.action !== "input") {
//           throw Error("Bad message: " + action);
//         }
//         const [handler_arg, inner_msg] = action.msg;
//         return [{ kind: "ready_to_raise", handler_arg }, { action: "continue", msg: inner_msg }];
//       }
//       if (state.kind === "ready_to_raise") {
//         return [{ kind: "process_response", handler_arg: state.handler_arg }, { action: "raise", msg: action }];
//       }
//       if (state.kind === "process_response") {
//         const [action, inner_msg] = action;
//         if (action === "result") {
//           return { action: "result", msg: [state.handler_arg, inner_msg], resume_state: { kind: "end" } };
//         } else {
//           return { action: "continue", msg: action, resume_state: { kind: "ready_to_handle", handler_arg: state.handler_arg } };
//         }
//       }
//       if (state.kind === "ready_to_handle") {
//         return { action: "continue", msg: [state.handler_arg, action], resume_state: { kind: "handling", handler_state: handler.init() } };
//       }
//       if (state.kind === "handling") {
//         const result = handler.run(state.handler_state, action);
//         if (result.action === "resume") {
//           const [handler_arg, inner_action, inner_arg] = result.msg;
//           return { action: "continue", msg: [inner_action, inner_arg], resume_state: { kind: "ready_to_raise", handler_arg } };
//         }
//         if (result.action === "raise") {
//           return { action: "raise", msg: result.msg, resume_state: { kind: "handling", handler_state: result.resume_state } };
//         }
//         if (result.action === "abort") {
//           const [handler_arg, inner_arg] = result.msg;
//           return { action: "result", msg: [handler_arg, inner_arg], resume_state: { kind: "end" } };
//         }
//         if (result.action === "continue") {
//           return { action: "continue", msg: result.msg, resume_state: { kind: "handling", handler_state: result.resume_state } };
//         }
//         unreachable(result.action);
//       }
//       throw Error('Bad state: ' + state.kind);
//     }
//   };
// }
// // type RetState = ["start"] | ["await_return"] | ["end"];

// // export const ret: Combinator<null, RetState> = {
// //   init(_: null): RetState {
// //     return ["start"];
// //   },
// //   run(state: RetState, msg: any): Result<RetState> {
// //     if (state.kind === "start") {
// //       return {
// //         action: "return",
// //         msg: msg,
// //         resume_state: ["await_return"],
// //       };
// //     }
// //     if (state.kind === "await_return") {
// //       return {
// //         action: "result",
// //         msg: msg,
// //         resume_state: ["end"],
// //       };
// //     }
// //     throw Error('Bad state: ' + state.kind);
// //   }
// // };

// export type IfThenElseState<T, F> = { kind: "start" } | { kind: "then", state: T } | { kind: "else", state: F };

// export function if_then_else<A, T, F>(then: Machine<T, A>, els: Machine<F, A>): Machine<IfThenElseState<T, F>, A | "continue"> {
//   return {
//     init() { return { kind: "start" }; },
//     trace(state: IfThenElseState<T, F>): string {
//       if (state.kind === "start") {
//         return "if(cond)";
//       }
//       if (state.kind === "then") {
//         return "if(true)" + then.trace(state.state);
//       }
//       if (state.kind === "else") {
//         return "if(false)" + els.trace(state.state);
//       }
//       unreachable(state);
//     },
//     run(state: IfThenElseState<T, F>, msg: any): Result<IfThenElseState<T, F>, A | "continue"> {
//       if (state.kind === "start") {
//         const [outer_state, cond] = msg;
//         if (cond) {
//           return {
//             action: "continue",
//             msg: outer_state,
//             resume_state: { kind: "then", state: then.init() },
//           };
//         } else {
//           return {
//             action: "continue",
//             msg: outer_state,
//             resume_state: { kind: "else", state: els.init() },
//           };
//         }
//       }
//       if (state.kind === "then") {
//         const result = then.run(state.state, msg);
//         return {
//           action: result.action,
//           msg: result.msg,
//           resume_state: { kind: "then", state: result.resume_state },
//         }
//       }
//       if (state.kind === "else") {
//         const result = els.run(state.state, msg);
//         return {
//           action: result.action,
//           msg: result.msg,
//           resume_state: { kind: "else", state: result.resume_state },
//         };
//       }
//       unreachable(state);
//     }
//   };
// }

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
    run(state: ClosureState<C, S>, msg: any): [ClosureState<C, S>, Action<any, any>] {
      if (state.kind === "in_constructor") {
        const [new_constructor_state, result] = constructor.run(state.constructor_state, msg);
        if (result.action === "result") {
          return [{ kind: "ready", arg: result.msg },{
            action: "result",
            msg: null,
          }]
        } else {
          return [{ kind: "in_constructor", constructor_state: new_constructor_state },{
            action: result.action,
            msg: result.msg,
          }]
        }
      }
      function run_inner(state: S, msg: Action<any, any>): [ClosureState<C, S>, Action<any, any>] {
        const [new_inner_state, result] = inner.run(state, msg);
        if (result.action === "result") {
          const [new_closure, new_output] = result.msg;
          return [{ kind: "ready", arg: new_closure },{
            action: "result",
            msg: new_output,
          }];
        }
        return [{ kind: "inner", inner: new_inner_state },{
          action: result.action,
          msg: result.msg,
        }];
      }
      if (state.kind === "ready") {
        if (msg.action !== "input") {
          throw Error("Bad message: " + msg);
        }
        return run_inner(inner.init(), { action: "input", msg: [state.arg, msg.msg] });
      }
      if (state.kind === "inner") {        
        if (msg.action !== "input") {
          throw Error("Bad message: " + msg);
        }
        return run_inner(state.inner, { action: "input", msg: msg.msg });
      }
      unreachable(state);
    }
  };
};
// // export function withInit<I, S>(value: I, inner: Combinator<I, S>): Combinator<null, S> {
// //   return {
// //     init(arg: null): S {
// //       return inner.init(value);
// //     },
// //     run(state: S, msg: any): Result<S> {
// //       return inner.run(state, msg);
// //     }
// //   };
// // }

// export type LoopState<S> = { kind: "inner", state: S } | { kind: "end" };
// export function loop<S>(inner: Machine<S, "break" | "continue" | "next" | "raise">): Machine<LoopState<S>, "result" | "continue" | "raise"> {
//   return {
//     init(): LoopState<S> {
//       return { kind: "inner", state: inner.init() };
//     },
//     trace(state: LoopState<S>): string {
//       if (state.kind === "inner") {
//         return "loop(" + inner.trace(state.state) + ")";
//       }
//       if (state.kind === "end") {
//         return "loop(end)";
//       }
//       unreachable(state);
//     },
//     run(state: LoopState<S>, msg: any): Result<LoopState<S>, "result" | "continue" | "raise"> {
//       if (state.kind === "inner") {
//         const result = inner.run(state.state, msg);

//         if (result.action === "next") {
//           return { action: "continue", msg: result.msg, resume_state: { kind: "inner", state: inner.init() } };
//         }
//         if (result.action === "break") {
//           return { action: "result", msg: result.msg, resume_state: { kind: "end" } };
//         }
//         if (result.action === "continue") {
//           return { action: "continue", msg: result.msg, resume_state: { kind: "inner", state: result.resume_state } };
//         }
//         if (result.action === "raise") {
//           return { action: "raise", msg: result.msg, resume_state: { kind: "inner", state: result.resume_state } };
//         }
//         unreachable(result.action);
//       }
//       throw Error('Bad state: ' + state.kind);
//     }
//   };
// }

// export const brk: Machine<null, "break"> = {
//   init() { return null },
//   trace(state: null): string {
//     return "brk";
//   },
//   run(state: null, msg: any): Result<null, "break"> {
//     return { action: "break", msg, resume_state: null };
//   }
// };


// export const next: Machine<null, "next"> = {
//   init() { return null },
//   trace(state: null): string {
//     return "next";
//   },
//   run(state: null, msg: any): Result<null, "next"> {
//     return { action: "next", msg, resume_state: null };
//   }
// };
// // export type HandleState<H, I> = ["inner", H, I] | ["handler", H, I] | ["end"];

// // export function handle<HI, H, II, I>(action: string, handler: Combinator<HI, H>, inner: Combinator<II, I>): Combinator<[HI, II], HandleState<H, I>> {
// //   return {
// //     init(arg: [HI, II]) {
// //       return ["inner", handler.init(arg[0]), inner.init(arg[1])];
// //     },
// //     run(state: HandleState<H, I>, msg: any): Result<HandleState<H, I>> {
// //       if (state.kind === "inner") {
// //         const handler_state = state[1];
// //         const inner_state = state[2];
// //         const result = inner.run(inner_state, msg);
// //         if (result.action === action) {
// //           return { action: "continue", msg: result.msg, resume_state: ["handler", handler_state, result.resume_state] };
// //         }
// //         return { action: result.action, msg: result.msg, resume_state: ["inner", handler_state, result.resume_state] };
// //       }
// //       if (state.kind === "handler") {
// //         const handler_state = state[1];
// //         const inner_state = state[2];
// //         const result = handler.run(handler_state, msg);
// //         if (result.action === "result") {
// //           return { action: "continue", msg: result.msg, resume_state: ["inner", result.resume_state, inner_state] };
// //         }
// //         return { action: result.action, msg: result.msg, resume_state: ["handler", result.resume_state, inner_state] };
// //       }
// //       throw Error('Bad state: ' + state.kind);
// //     }
// //   };
// // }

// // export type ConstructState<S> = ["start"] | ["inner", S];

// // export function construct<S>(inner: Combinator<unknown, S>): Combinator<null, ConstructState<S>> {
// //   return {
// //     init(_: null): ConstructState<S> {
// //       return ["start"];
// //     },
// //     run(state: ConstructState<S>, msg: any): Result<ConstructState<S>> {
// //       if (state.kind === "start") {
// //         const [state, inner_msg] = msg;
// //         return { action: "continue", msg: inner_msg, resume_state: ["inner", inner.init(state)] };
// //       }
// //       if (state.kind === "inner") {
// //         const inner_state = state[1];
// //         const result = inner.run(inner_state, msg);
// //         return { action: result.action, msg: result.msg, resume_state: ["inner", result.resume_state] };
// //       }
// //       throw Error('Bad state: ' + state.kind);
// //     }
// //   };
// // }

// // type CurryState<I, S> = ["await_init", unknown] | ["transform_init", FuncState<I>, unknown] | ["inner", FuncState<S>] | ["ready", FuncState<S>, unknown];

// // export function curryState<I, S>(stateInit: Machine<FuncState<I>>, machine: Machine<FuncState<S>>): Machine<FuncState<CurryState<I, S>>> {
// //   return (state: FuncState<CurryState<I, S>>, msg: any): Result<FuncState<CurryState<I, S>>> => {
// //     if (state.kind === "start") {
// //       return { action: "input", msg: ["clone"], resume_state: ["inner", ["await_init", msg]] };
// //     }
// //     if (state.kind === "inner") {
// //       const curry_state = state[1];
// //       if (curry_state.kind === "await_init") {
// //         const deferred_msg = curry_state[1];
// //         return { action: "continue", msg, resume_state: ["inner", ["transform_init", ["start"], deferred_msg]] };
// //       }
// //       if (curry_state.kind === "transform_init") {
// //         const init_state = curry_state[1];
// //         const deferred_msg = curry_state[2];
// //         const result = stateInit(init_state, msg);
// //         if (result.action === "result") {
// //           return { action: "continue", msg: [result.msg, deferred_msg], resume_state: ["inner", ["inner", ["start"]]] };
// //         }
// //         return { action: result.action, msg: result.msg, resume_state: ["inner", ["transform_init", result.resume_state, deferred_msg]] };
// //       }
// //       if (curry_state.kind === "inner") {
// //         const inner_state = curry_state[1];
// //         const result = machine(inner_state, msg);
// //         if (result.action === "result") {
// //           const [inner_arg, inner_msg] = result.msg;
// //           return { action: "result", msg: inner_msg, resume_state: ["inner", ["ready", result.resume_state, inner_arg]] };
// //         }
// //         return { action: result.action, msg: result.msg, resume_state: ["inner", ["inner", result.resume_state]] };
// //       }
// //       if (curry_state.kind === "ready") {
// //         const inner_state = curry_state[1];
// //         const inner_arg = curry_state[2];
// //         return { action: "continue", msg: [inner_arg, msg], resume_state: ["inner", ["inner", inner_state]] };
// //       }
// //       throw Error('Bad state: ' + curry_state.kind);
// //     }
// //     throw Error('Bad state: ' + state.kind);
// //   };
// // }