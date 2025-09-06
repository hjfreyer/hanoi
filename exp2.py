
from dataclasses import dataclass
from functools import wraps
from typing import Any, Callable, Literal, Protocol


@dataclass
class Result:
    action: str
    action_args: Any
    resume_state: tuple[str, Any]

Machine = Callable[[Any, Any], Result]


@dataclass
class ForLoop:
    body: Machine

    def __call__(self, state: tuple[str, Any], msg: Any) -> Result:
        def call_body(state: tuple[str, Any], msg: Any) -> Result:
            body_result = self.body(state, msg)
            if body_result.action == 'next_loop':
                return Result('continue', body_result.action_args, ('body', ('start', ())))
            elif body_result.action == 'break':
                return Result('result', body_result.action_args, ('end', None))
            else:
                return Result(body_result.action, body_result.action_args, ('body', body_result.resume_state))

        if state[0] == 'start':
            return call_body(('start', state[1]), msg)
        elif state[0] == 'body':
            inner_state_tag, inner_state_args = state[1]
            return call_body((inner_state_tag, inner_state_args), msg)
        else:
            assert False, "Bad state: "+state[0]

@dataclass
class HandlerResume:
    kind: Literal['resume']
    handler_state: tuple[str, Any]
    msg: Any

@dataclass
class HandlerContinue:
    kind: Literal['continue']
    action: str
    msg: Any
    handler_state: tuple[str, Any]


class Handler(Protocol):
    def handle(self, handler_name: str, handler_state: tuple[str, Any], msg: Any) -> HandlerResume | HandlerContinue:
        ...



@dataclass
class ImplHandler:
    inner: Machine

    def handle(self, handler_name: str, handler_state: tuple[str, Any], msg: Any) -> HandlerResume | HandlerContinue:
        result = self.inner(handler_state, msg)
        if result.action == 'result':
            return HandlerResume('resume', result.resume_state, result.action_args)
        else:
            return HandlerContinue('continue', result.action, result.action_args, result.resume_state)


@dataclass
class AndThen:
    inner: Machine

    def handle(self, handler_name: str, handler_state: tuple[str, Any], msg: Any) -> HandlerResume | HandlerContinue:
        result = self.inner(handler_state, msg)
        return HandlerContinue('continue', result.action, result.action_args, result.resume_state)

@dataclass
class PassThroughHandler:
    def handle(self, handler_name: str, handler_state: tuple[str, Any], msg: Any) -> HandlerResume | HandlerContinue:
        if handler_state[0] == 'start':
            return HandlerContinue('continue', handler_name, msg, ('awaiting', None))
        elif handler_state[0] == 'awaiting':
            return HandlerResume('resume', ('start', ()), msg)
        else:
            assert False, "Bad state: "+handler_state[0]


# @dataclass
# class OneWayHandler:
#     handler_name: str

#     def __call__(self, state_tag: str, state_args: Any, msg: Any) -> Result:
#         assert state_tag == 'start', "Bad state: "+state_tag
#         return Result(self.handler_name, msg, ('end', None))

@dataclass
class Bound:
    inner: Machine
    handlers: dict[str, Handler]

    def __call__(self, state: tuple[str, Any], msg: Any) -> Result:
        def call_handler(handler_name: str, msg: Any, inner_state: tuple[str, Any], handler_states: dict[str, tuple[str, Any]]) -> Result:
            handler = self.handlers[handler_name]
            handler_state = handler_states[handler_name]
            handler_result = handler.handle(handler_name, handler_state, msg)
            handler_states |= {handler_name: handler_result.handler_state}
            if handler_result.kind == 'resume':
                return Result('continue', handler_result.msg, ('inner', (inner_state, handler_states)))
            elif handler_result.kind == 'continue':
                return Result(handler_result.action, handler_result.msg, ('handler', (handler_name, inner_state, handler_states)))
            else:
                assert False, "Bad handler result: "+str(handler_result)
        def call_inner(inner_state: tuple[str, Any], msg: Any, handler_states: dict[str, tuple[str, Any]]) -> Result:
            inner_result = self.inner(inner_state, msg)
            return Result('continue', inner_result.action_args, ('handler', (inner_result.action, inner_result.resume_state, handler_states)))
        if state[0] == 'start':
            return Result('continue', msg, ('inner', (('start', state[1]), {k: ('start', ()) for k in self.handlers})))
        elif state[0] == 'inner':
            inner_state, handler_states = state[1]
            return call_inner(inner_state, msg, handler_states)
        elif state[0] == 'handler':
            handler_name, inner_state, handler_states = state[1]
            return call_handler(handler_name, msg, inner_state, handler_states)
        else:
            assert False, "Bad state: "+state[0]


def transformer(f: Callable[[Any], Any]) -> Machine:
    @wraps(f)
    def run(state: tuple[str, Any], msg: Any) -> Result:
        assert state[0] == 'start', "Bad state: "+state[0]
        value = msg
        return Result('result', f(value), ('end', None))
    return run


def single_state(f: Callable[[Any], tuple[str, Any]]) -> Machine:
    @wraps(f)
    def run(state: tuple[str, Any], msg: Any) -> Result:
        assert state[0] == 'start', "Bad state: "+state[0]
        action, action_args = f(msg)
        return Result(action, action_args, ('end', None))
    return run


@dataclass
class IfThenElse:
    then: Machine
    els: Machine

    def __call__(self, state: tuple[str, Any], msg: Any) -> Result:

        def call_then(state: tuple[str, Any], msg: Any) -> Result:
            result = self.then(state, msg)
            return Result(result.action, result.action_args, ('then', result.resume_state))

        def call_els(state: tuple[str, Any], msg: Any) -> Result:
            result = self.els(state, msg)
            return Result(result.action, result.action_args, ('else', result.resume_state))

        if state[0] == 'start':
            (smuggled, cond) = msg
            if cond:
                return call_then(('start', state[1]), smuggled)
            else:
                return call_els(('start', state[1]), smuggled)
        elif state[0] == 'then':
            inner_state_tag, inner_state_args = state[1]
            return call_then((inner_state_tag, inner_state_args), msg)
        elif state[0] == 'else':
            inner_state_tag, inner_state_args = state[1]
            return call_els((inner_state_tag, inner_state_args), msg)
        else:
            assert False, "Bad state: "+state[0]

# f := Bound(g, {
#        iter_next: RaiseWithCallback(h)
#      }
#  - f is called with "start"
#    - f calls g with "start"
#      - g raises "iter_next" (with g_state)
#    - f becomes RaiseWithCallback(h) with g_state
#    - RaiseWithCallback(h) raises "iter_next" (with "awaiting")
#  - f is called with ("in iter_next", "awaiting") and iter_next_res
#    - RaiseWithCallback(h) becomes h with "start" and iter_next_res



# f := Bound(g, {
#        iter_next: RaiseAndResume,
#        result: OneWay(h)
#      }
#  - f is called with "start"
#    - f calls g with "start"
#      - g raises "iter_next" (with g_state)
#    - f becomes RaiseAndResume with g_state
#    - RaiseAndResume raises "iter_next" (with g_state)
#  - f is called with ("in_iter_next", g_state) and iter_next_res
#    - RaiseAndResume raises "continue" with ("inner", g_state) and iter_next_res
#  - f is called with ("inner", g_state) and iter_next_res
#    - f calls g with g_state and iter_next_res
#      - g raises "result" with g_res
#    - f becomes OneWay(h) with g_state and g_res
#    - OneWay(h) calls h with "start" and g_res

# f := Bound(g, {
#        iter_next: ConcreteImpl,
#        result: h
#      }
#  - f is called with "start"
#    - f calls g with "start"
#      - g raises "iter_next" (with g_state)
#    - f calls ConcreteImpl
#      - ConcreteImpl raises "result"
#  - f is called with (f_state, g_state) and iter_next_res
#    - f calls g with g_state and iter_next_res
#      - g raises "result" with g_res
#    - f becomes h with "start" and g_res

# 