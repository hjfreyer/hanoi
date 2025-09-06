from dataclasses import dataclass
from functools import wraps
from typing import Any, Callable, Literal, Protocol
import unittest


@dataclass
class Result:
    action: str
    action_args: Any
    resume_state: tuple[str, Any]


def str_len(state: tuple[str, Any], msg: Any) -> Result:
    assert state[0] == 'start'
    s = msg
    return Result('result', len(s), ('end', None))



def str_iter(state: tuple[str, Any], msg: Any) -> Result:
    if state[0] == 'start':
        s = msg
        return Result('result', (), ('ready', (s, -1)))
    elif state[0] == 'ready':
        iter = state[1]
        if msg[0] == 'next':
            return str_iter_next(iter)
        elif msg[0] == 'clone':
            return str_iter_clone(iter)
        else:
            assert False, "Bad msg: "+str(msg)
    else:
        assert False, "Bad state: "+str(state)



def str_iter_next(msg: Any) -> Result:
    s, offset = msg
    offset += 1

    str_len_result = str_len(('start', ()), s)
    assert str_len_result.action == 'result'
    strlen = str_len_result.action_args

    if offset == strlen:
        return Result('result', False, ('ready', (s, offset)))
    else:
        return Result('result', True, ('ready', (s, offset)))


def str_iter_clone(msg: Any) -> Result:
    s, offset = msg
    return Result('result', s[offset], ('ready', msg))


def str_iter_equals_body(state: tuple[str, Any], msg: Any) -> Result:
    if state[0] == 'start':
        s, offset = msg
        return Result('iter', ('next', None), ('iter_next_cb', (s, offset)))
    elif state[0] == 'iter_next_cb':
        s, offset = state[1]
        iter_has_next = msg
        str_has_next = offset < len(s)

        if not iter_has_next and not str_has_next:
            return Result('break', True, ('end', None))
        elif not iter_has_next or not str_has_next:
            return Result('break', False, ('end', None))
        else:
            return Result('iter', ('clone', None), ('iter_clone_cb', (s, offset)))
    elif state[0] == 'iter_clone_cb':
        s, offset = state[1]
        iter_char = msg
        str_char = s[offset]
        if iter_char == str_char:
            return Result('next_loop', (s, offset + 1), ('end', None))
        else:
            return Result('break', False, ('end', None))
    else:
        assert False, "Bad state: "+state[0]

Machine = Callable[[tuple[str, Any], Any], Result]


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
            return call_handler(inner_result.action, inner_result.action_args, inner_result.resume_state, handler_states)
        if state[0] == 'start':
            return call_inner(('start', state[1]), msg, {k: ('start', ()) for k in self.handlers})
        elif state[0] == 'inner':
            inner_state, handler_states = state[1]
            return call_inner(inner_state, msg, handler_states)
        elif state[0] == 'handler':
            handler_name, inner_state, handler_states = state[1]
            return call_handler(handler_name, msg, inner_state, handler_states)
        else:
            assert False, "Bad state: "+state[0]


def str_iter_equals_preamble(state: tuple[str, Any], msg: Any) -> Result:
    assert state[0] == 'start', "Bad state: "+state[0]
    s = msg
    return Result('result', (s, 0), ('end', None))


str_iter_equals = Bound(str_iter_equals_preamble, {
    'result': AndThen(ForLoop(str_iter_equals_body)),
})


def str_iter_equals_inverse_preamble(state: tuple[str, Any], msg: Any) -> Result:
    assert state[0] == 'start', "Bad state: "+state[0]
    s = msg
    return Result('result', (s, (s, -1)), ('end', None))


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

string_iter_equals_inverse = Bound(str_iter_equals_inverse_preamble, {
    'result': AndThen(Bound(str_iter_equals, {
        'iter_next': ImplHandler(str_iter_next),
        'iter_clone': ImplHandler(str_iter_clone),
        'continue': PassThroughHandler(),
        'result': PassThroughHandler()
    }))})

@transformer
def string_separated_values_new(iter: Any) -> Any:
    return ('unstarted', iter)


def string_separated_values_next(state: tuple[str, Any], msg: Any) -> Result:
    assert state[0] == 'start', "Bad state: "+state[0]
    iter_state, iter_args = msg
    if iter_state == 'unstarted':
        inner_iter = iter_args
        return Result('result', (('inner_unstarted', inner_iter), True), ('end', None))
    else:
        assert False, "Bad iter state: "+iter_state


@single_state
def string_separated_values_inner_next_preamble1(iter: Any) -> tuple[str, Any]:
    iter_tag, iter_args = iter
    if iter_tag == 'inner_unstarted':
        return ('iter_next', iter_args)
    else:
        assert False, "Bad iter state: "+iter_tag


@single_state
def string_separated_values_inner_next_preamble2(iter_and_bool: Any) -> tuple[str, Any]:
    iter, iter_has_next = iter_and_bool
    if iter_has_next:
        return ('iter_clone', iter)
    else:
        return ('result', (('unstarted', iter), False))


string_separated_values_inner_next = Bound(
    string_separated_values_inner_next_preamble1,
    {
        'iter_next': PassThroughHandler(),
    }
)

def emit_twice(state: tuple[str, Any], msg: Any) -> Result:
    if state[0] == 'start':
        return Result('get_items', None, ('await_items', msg))
    elif state[0] == 'await_items':
        prev_msg = state[1]
        return Result('continue', prev_msg, ('at', (-1, msg)))
    elif state[0] == 'at':
        at, items = state[1]
        if msg[0] == 'next':
            at += 1
            return Result('result', at < 2, ('at', (at, items)))
        elif msg[0] == 'clone':
            return Result('result', items[at], state)
        else:
            assert False, "Bad msg: "+str(msg)
    else:
        assert False, "Bad state: "+str(state)

def result_second(state: tuple[str, Any], msg: Any) -> Result:
    if state[0] == 'start':
        return Result('iter', ('next', None), ('wait1', None))
    elif state[0] == 'wait1':
        return Result('iter', ('next', None), ('wait2', None))
    elif state[0] == 'wait2':
        return Result('iter', ('clone', None), ('wait3', None))
    elif state[0] == 'wait3':
        return Result('result', msg, ('end', None))
    else:
        assert False, "Bad state: "+str(state)

twice_test = Bound(result_second, {
    'iter': ImplHandler(Bound(emit_twice, {
        'get_items': ImplHandler(transformer(lambda x: ("foo", "bar"))),
        'continue': PassThroughHandler(),
        'result': PassThroughHandler(),
    })),
    'result': PassThroughHandler(),
})

def assertTranscript(test: unittest.TestCase, machine: Any, transcript: list[tuple[Any, str, Any]]):
    state = ('start', ())
    while transcript:
        (input, result_tag, result_args) = transcript.pop(0)
        result = machine(state, input)
        while result.action == 'continue':
            result = machine(result.resume_state, result.action_args)
        test.assertEqual(result.action, result_tag)
        test.assertEqual(result.action_args, result_args)
        state = result.resume_state


class TestMisc(unittest.TestCase):

    def test_emit_twice(self):
        transcript: list[tuple[Any, str, Any]] = [
            (('next', None), 'get_items', None),
            (('foo', 'bar'), 'result', True),
            (('clone', None), 'result', 'foo'),
            (('next', None), 'result', True),
            (('clone', None), 'result', 'bar'),
            (('next', None), 'result', False),
        ]
        assertTranscript(self, emit_twice, transcript)

    def test_result_second(self):
        transcript: list[tuple[Any, str, Any]] = [
            (None, 'iter', ('next', None)),
            (True, 'iter', ('next', None)),
            (True, 'iter', ('clone', None)),
            ('foo', 'result', 'foo'),
        ]
        assertTranscript(self, result_second, transcript)

    def test_twice(self):
        transcript: list[tuple[Any, str, Any]] = [
            (None, 'result', 'bar'),
        ]
        assertTranscript(self, twice_test, transcript)

class TestStringIter(unittest.TestCase):
    def test_next(self):
        transcript: list[tuple[Any, str, Any]] = [
            ('foo', 'result', ()),
            (('next', ()), 'result', True),
        ]
        assertTranscript(self, str_iter, transcript)

    def test_clone(self):
        transcript: list[tuple[Any, str, Any]] = [
            ('foo', 'result', ()),
            (('next', ()), 'result', True),
            (('clone', ()), 'result', 'f'),
        ]
        assertTranscript(self, str_iter, transcript)


class TestStringIterEquals(unittest.TestCase):

    def test_success(self):
        transcript: list[tuple[Any, str, Any]] = [
            ('foo', 'iter', ('next', None)),
            (True, 'iter', ('clone', None)),
            ('f', 'iter', ('next', None)),
            (True, 'iter', ('clone', None)),
            ('o', 'iter', ('next', None)),
            (True, 'iter', ('clone', None)),
            ('o', 'iter', ('next', None)),
            (False, 'result', True)
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_iter_shorter_than_string(self):
        transcript: list[tuple[Any, str, Any]] = [
            ('foo', 'iter', ('next', None)),
            ( True, 'iter', ('clone', None)),
            ( 'f', 'iter', ('next', None)),
            ( True, 'iter', ('clone', None)),
            ( 'o', 'iter', ('next', None)),
            ( False, 'result', False)
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_string_shorter_than_iter(self):
        transcript: list[tuple[Any, str, Any]] = [
            ('f', 'iter', ('next', None)),
            (True, 'iter', ('clone', None)),
            ('f', 'iter', ('next', None)),
            (True, 'result', False)
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_char_mismatch(self):
        transcript: list[tuple[Any, str, Any]] = [
            ('foo', 'iter', ('next', None)),
            (True, 'iter', ('clone', None)),
            ('f', 'iter', ('next', None)),
            (True, 'iter', ('clone', None)),
            ('r', 'result', False)
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_inverse(self):
        transcript: list[tuple[Any, str, Any]] = [
            ('foo', 'result', True)
        ]
        assertTranscript(self, string_iter_equals_inverse, transcript)

class TestStringSeparatedValues(unittest.TestCase):
    # def test_empty(self):
    #     # transcript1: list[tuple[Any, str, Any]] = [
    #     #     ('iter', 'result', ('unstarted', 'iter'))
    #     # ]
    #     # assertTranscript(self, string_separated_values_new, transcript1)

    #     # transcript2: list[tuple[Any, str, Any]] = [
    #     #     (('unstarted', 'iter'), 'result', (('inner_unstarted', 'iter'), True))
    #     # ]
    #     # assertTranscript(self, string_separated_values_next, transcript2)

    #     transcript3: list[tuple[Any, str, Any]] = [
    #         (('inner_unstarted', 'iter'), 'iter_next', 'iter'),
    #         (('iter', False), 'result', ('foo', False))
    #     ]
    #     assertTranscript(self, string_separated_values_inner_next, transcript3)
    pass
if __name__ == '__main__':
    unittest.main()
