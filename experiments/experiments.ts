import { assert } from "console";

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
