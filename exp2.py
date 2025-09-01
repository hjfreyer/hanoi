from dataclasses import dataclass
from typing import Any, Callable
import unittest


@dataclass
class Result:
    action: str
    action_args: Any
    resume_state_tag: str
    resume_state_args: Any

def str_len(state_tag: str, state_args: Any, msg: Any) -> Result:
    assert state_tag == 'start'
    s = msg
    return Result('result', len(s), 'end', None)

def str_iter_next(state_tag: str, state_args: Any, msg: Any) -> Result:
    assert state_tag == 'start'
    s, offset = msg
    offset += 1

    str_len_result = str_len('start', (), s)
    assert str_len_result.action == 'result'
    strlen = str_len_result.action_args

    if offset == strlen:
        return Result('result', ((s, offset), False), 'end', None)
    else:
        return Result('result', ((s, offset), True), 'end', None)

def str_iter_clone(state_tag: str, state_args: Any, msg: Any) -> Result:
    assert state_tag == 'start'
    s, offset = msg
    return Result('result', (msg, s[offset]), 'end', None)


def str_iter_equals_body(state_tag: str, state_args: Any, msg: Any) -> Result:
    if state_tag == 'start':
        s, offset, iter = msg
        return Result('iter_next', iter, 'iter_next_cb', (s, offset))
    elif state_tag == 'iter_next_cb':
        s, offset = state_args
        iter, iter_has_next = msg
        str_has_next = offset < len(s)

        if not iter_has_next and not str_has_next:
            return Result('break', True, 'end', None)
        elif not iter_has_next or not str_has_next:
            return Result('break', False, 'end', None)
        else:
            return Result('iter_clone', iter, 'iter_clone_cb', (s, offset))
    elif state_tag == 'iter_clone_cb':
        s, offset = state_args
        iter, iter_char = msg
        str_char = s[offset]
        if iter_char == str_char:
            return Result('next_loop', (s, offset + 1, iter), 'end', None)
        else:
            return Result('break', False, 'end', None)
    else:
        assert False, "Bad state: "+state_tag

@dataclass
class ForLoop:
    body : Callable[[str, Any, Any], Result]

    def __call__(self, state_tag: str, state_args: Any, msg: Any) -> Result:
        def call_body(state_tag: str, state_args: Any, msg: Any) -> Result:
            body_result = self.body(state_tag, state_args, msg)
            if body_result.action == 'next_loop':
                return Result('continue', body_result.action_args, 'body', ('start', ()))
            elif body_result.action == 'break':
                return Result('result', body_result.action_args, 'end', None)
            else:
                return Result(body_result.action, body_result.action_args, 'body', (body_result.resume_state_tag, body_result.resume_state_args))
        
        if state_tag == 'start':
            return call_body('start', state_args, msg)  
        elif state_tag == 'body':
            inner_state_tag, inner_state_args = state_args
            return call_body(inner_state_tag, inner_state_args, msg)
        else:
            assert False, "Bad state: "+state_tag

@dataclass
class Bound:
    inner : Callable[[str, Any, Any], Result]
    handlers : dict[str, Callable[[str, Any, Any], Result]]

    def __call__(self, state_tag: str, state_args: Any, msg: Any) -> Result:
        def call_handler(handler_name: str, msg: Any, handler_state_tag: str, handler_state_args: Any, inner_state_tag: str, inner_state_args: Any) -> Result:
            handler = self.handlers[handler_name]
            handler_result = handler(handler_state_tag, handler_state_args, msg)
            if handler_result.action == 'resume':
                return Result('continue', handler_result.action_args, 'inner', (inner_state_tag, inner_state_args))
            else:
                return Result(handler_result.action, handler_result.action_args, 'handler', (handler_name, handler_result.resume_state_tag, handler_result.resume_state_args, inner_state_tag, inner_state_args))
        def call_inner(state_tag: str, state_args: Any, msg: Any) -> Result:
            inner_result = self.inner(state_tag, state_args, msg)
            return call_handler(inner_result.action, inner_result.action_args, 'start', (), inner_result.resume_state_tag, inner_result.resume_state_args)
        if state_tag == 'start':
            return call_inner('start', state_args, msg)
        elif state_tag == 'inner':
            inner_state_tag, inner_state_args = state_args
            return call_inner(inner_state_tag, inner_state_args, msg)
        elif state_tag == 'handler':
            handler_name, handler_state_tag, handler_state_args, inner_state_tag, inner_state_args = state_args
            return call_handler(handler_name, msg, handler_state_tag, handler_state_args, inner_state_tag, inner_state_args)
        else:
            assert False, "Bad state: "+state_tag



def str_iter_equals_preamble(state_tag: str, state_args: Any, msg: Any) -> Result:
    assert state_tag == 'start'
    s, iter = msg
    return Result('result', (s, 0, iter), 'end', None)

str_iter_equals = Bound(str_iter_equals_preamble, {
    'result': ForLoop(str_iter_equals_body),
})


def assertTranscript(test : unittest.TestCase, machine : Any, transcript : list[tuple[Any, str, Any]]):
    state_tag = 'start'
    state_args = ()
    while transcript:
        (input, result_tag, result_args) = transcript.pop(0)
        result = machine(state_tag, state_args, input)
        while result.action == 'continue':
            result = machine(result.resume_state_tag, result.resume_state_args, result.action_args)
        test.assertEqual(result.action, result_tag)
        test.assertEqual(result.action_args, result_args)
        state_tag = result.resume_state_tag
        state_args = result.resume_state_args
        

class TestStringIter(unittest.TestCase):
    def test_next(self):
        transcript : list[tuple[Any, str, Any]] = [
            (('foo', -1), 'result', (('foo', 0), True)),
        ]
        assertTranscript(self, str_iter_next, transcript)

    def test_clone(self):
        transcript : list[tuple[Any, str, Any]] = [
            (('foo', 0), 'result', (('foo', 0), 'f')),
        ]
        assertTranscript(self, str_iter_clone, transcript)


class TestStringIterEquals(unittest.TestCase):
    
    def test_success(self):
        transcript : list[tuple[Any, str, Any]] = [
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
        transcript : list[tuple[Any, str, Any]] = [
            (('foo', 'iter'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'f'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'o'), 'iter_next', 'iter'),
            (('iter', False), 'result', False)
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_string_shorter_than_iter(self):
        transcript : list[tuple[Any, str, Any]] = [
            (('f', 'iter'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'f'), 'iter_next', 'iter'),
            (('iter', True), 'result', False)
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_char_mismatch(self):
        transcript : list[tuple[Any, str, Any]] = [
            (('foo', 'iter'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'f'), 'iter_next', 'iter'),
            (('iter', True), 'iter_clone', 'iter'),
            (('iter', 'r'), 'result', False)
        ]
        assertTranscript(self, str_iter_equals, transcript)

if __name__ == '__main__':
    unittest.main()
