from dataclasses import dataclass
from typing import Any
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

def str_iter_equals(state_tag: str, state_args: Any, msg: Any) -> Result:
    if state_tag == 'start':
        s, iter = msg
        return Result('continue', (), 'loop_body', (s, 0, iter))
    elif state_tag == 'loop_body':
        s, offset, iter = state_args
        return Result('iter_next', iter, 'iter_next_cb', (s, offset))
    elif state_tag == 'iter_next_cb':
        s, offset = state_args
        iter, iter_has_next = msg
        str_has_next = offset < len(s)

        if not iter_has_next and not str_has_next:
            return Result('result', True, 'end', None)
        elif not iter_has_next or not str_has_next:
            return Result('result', False, 'end', None)
        else:
            return Result('iter_clone', iter, 'iter_clone_cb', (s, offset))
    elif state_tag == 'iter_clone_cb':
        s, offset = state_args
        iter, iter_char = msg
        str_char = s[offset]
        if iter_char == str_char:
            return Result('continue', (), 'loop_body', (s, offset + 1, iter))
        else:
            return Result('result', False, 'end', None)
    else:
        assert False, "Bad state: "+state_tag


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
