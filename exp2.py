from dataclasses import dataclass
from functools import wraps
from typing import Any, Callable
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


def str_iter_next(state: tuple[str, Any], msg: Any) -> Result:
    assert state[0] == 'start'
    s, offset = msg
    offset += 1

    str_len_result = str_len(('start', ()), s)
    assert str_len_result.action == 'result'
    strlen = str_len_result.action_args

    if offset == strlen:
        return Result('result', ((s, offset), False), ('end', None))
    else:
        return Result('result', ((s, offset), True), ('end', None))


def str_iter_clone(state: tuple[str, Any], msg: Any) -> Result:
    assert state[0] == 'start'
    s, offset = msg
    return Result('result', (msg, s[offset]), ('end', None))


def str_iter_equals_body(state: tuple[str, Any], msg: Any) -> Result:
    if state[0] == 'start':
        s, offset, iter = msg
        return Result('iter_next', iter, ('iter_next_cb', (s, offset)))
    elif state[0] == 'iter_next_cb':
        s, offset = state[1]
        iter, iter_has_next = msg
        str_has_next = offset < len(s)

        if not iter_has_next and not str_has_next:
            return Result('break', True, ('end', None))
        elif not iter_has_next or not str_has_next:
            return Result('break', False, ('end', None))
        else:
            return Result('iter_clone', iter, ('iter_clone_cb', (s, offset)))
    elif state[0] == 'iter_clone_cb':
        s, offset = state[1]
        iter, iter_char = msg
        str_char = s[offset]
        if iter_char == str_char:
            return Result('next_loop', (s, offset + 1, iter), ('end', None))
        else:
            return Result('break', False, ('end', None))
    else:
        assert False, "Bad state: "+state[0]

Machine = Callable[[tuple[str, Any], Any], Result]
Handler = Callable[[Any, Any], Result]


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
class ImplHandler:
    inner: Machine

    def __call__(self, state: tuple[str, Any], msg: Any) -> Result:
        handler_name, handler_state_args, caller_state = state[1]
        result = self.inner((state[0], handler_state_args), msg)
        if result.action == 'result':
            return Result('continue', result.action_args, ('inner', caller_state))
        else:
            return Result(result.action, result.action_args, ('handler', (handler_name, result.resume_state, caller_state)))


@dataclass
class AndThen:
    inner: Machine

    def __call__(self, state: tuple[str, Any], msg: Any) -> Result:
        handler_name, handler_state_args, caller_state = state[1]
        result = self.inner((state[0], handler_state_args), msg)
        return Result(result.action, result.action_args, ('handler', (handler_name, result.resume_state, caller_state)))

@dataclass
class PassThroughHandler:
    def __call__(self, state: tuple[str, Any], msg: Any) -> Result:
        assert state[0] == 'start', "Bad state: "+state[0]
        handler_name, handler_state_args, caller_state = state[1]
        return Result(handler_name, msg, ('inner', caller_state))


# @dataclass
# class OneWayHandler:
#     handler_name: str

#     def __call__(self, state_tag: str, state_args: Any, msg: Any) -> Result:
#         assert state_tag == 'start', "Bad state: "+state_tag
#         return Result(self.handler_name, msg, ('end', None))

@dataclass
class Bound:
    inner: Machine
    handlers: dict[str, Machine]

    def __call__(self, state: tuple[str, Any], msg: Any) -> Result:
        def call_handler(handler_name: str, msg: Any, handler_state: tuple[str, Any], caller_state: tuple[str, Any]) -> Result:
            handler = self.handlers[handler_name]
            return handler((handler_state[0], (handler_name, handler_state[1], caller_state)), msg)
        def call_inner(state: tuple[str, Any], msg: Any) -> Result:
            inner_result = self.inner(state, msg)
            return call_handler(inner_result.action, inner_result.action_args, ('start', ()), inner_result.resume_state)
        if state[0] == 'start':
            return call_inner(('start', state[1]), msg)
        elif state[0] == 'inner':
            inner_state_tag, inner_state_args = state[1]
            return call_inner((inner_state_tag, inner_state_args), msg)
        elif state[0] == 'handler':
            handler_name, handler_state, caller_state = state[1]
            return call_handler(handler_name, msg, handler_state, caller_state)
        else:
            assert False, "Bad state: "+state[0]


def str_iter_equals_preamble(state: tuple[str, Any], msg: Any) -> Result:
    assert state[0] == 'start', "Bad state: "+state[0]
    s, iter = msg
    return Result('result', (s, 0, iter), ('end', None))


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


class TestStringIter(unittest.TestCase):
    def test_next(self):
        transcript: list[tuple[Any, str, Any]] = [
            (('foo', -1), 'result', (('foo', 0), True)),
        ]
        assertTranscript(self, str_iter_next, transcript)

    def test_clone(self):
        transcript: list[tuple[Any, str, Any]] = [
            (('foo', 0), 'result', (('foo', 0), 'f')),
        ]
        assertTranscript(self, str_iter_clone, transcript)


class TestStringIterEquals(unittest.TestCase):

    def test_success(self):
        transcript: list[tuple[Any, str, Any]] = [
            (('foo', 'iter'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'f'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'o'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'o'), 'iter_next', 'iter'),
            (('iter', False), 'result', True)
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_iter_shorter_than_string(self):
        transcript: list[tuple[Any, str, Any]] = [
            (('foo', 'iter'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'f'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'o'), 'iter_next', 'iter'),
            (('iter', False), 'result', False)
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_string_shorter_than_iter(self):
        transcript: list[tuple[Any, str, Any]] = [
            (('f', 'iter'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'f'), 'iter_next', 'iter'),
            (('iter', True), 'result', False)
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_char_mismatch(self):
        transcript: list[tuple[Any, str, Any]] = [
            (('foo', 'iter'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'f'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'r'), 'result', False)
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
