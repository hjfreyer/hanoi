#!/usr/bin/env python3
"""
Sample Python unittest module for experiment testing.
This module demonstrates proper unittest structure and patterns.
"""

import unittest
import sys
from typing import Tuple, Any, Optional



def smuggle(machine):
    def impl(state, msg):
        state_tag, state_args = state
        if state_tag == 'start':
            smuggled, rest = msg
            return (('run', (smuggled, ('start', ()))), ('continue', rest))
        elif state_tag == 'run':
            (smuggled, inner_state) = state_args
            inner_state, (inner_msg_tag, inner_msg_args) = machine(inner_state, msg)
            if inner_msg_tag in ['continue', 'other']:
                return (('run', (smuggled, inner_state)), (inner_msg_tag, inner_msg_args))
            elif inner_msg_tag == 'result':
                return (('end', ()), ('result', (smuggled, inner_msg_args)))
            else:
                assert False, "Bad message"
    return impl



# def bind(machine, handler):
#     def impl(state, msg):
#         state_tag, state_args = state
#         if state_tag == 'start':
#             return (('run', ('start', msg)), ('pass', ()))
#         elif state_tag == 'run':
#             inner_state, inner_msg = state_args
#             inner_state, inner_msg = machine(inner_state, inner_msg)
#             return (('run_handler', ('start', inner_msg)), ('pass', ()))
#         elif state_tag == 'run_handler':
#             handler_state, handler_msg = state_args
#             handler_state, (handler_msg_tag, handler_msg_args) = handler(handler_state, handler_msg)
#             if handler_msg_tag == 'result':
#                 return (('end', ()), ('result', handler_msg_args))
#             elif handler_msg_tag == 'raise':
#                 return (('paused', (inner_state, handler_state)), handler_msg_args)
#             else:
#                 assert False, "Bad state"
#         elif state_tag == 'paused':
#             inner_state, handler_state = state_args
#             return (('run', ('paused', (inner_state, handler_state))), ('pass', ()))
#         else:
#             assert False, "Bad state"
#     return impl

def for_loop(machine):
    def impl(state, msg):
        state_tag, state_args = state
        if state_tag == 'start':
            return (('run', ('start', ())), ('continue', msg))
        elif state_tag == 'run':
            inner_state = state_args
            inner_state, (inner_msg_tag, inner_msg_args) = machine(inner_state, msg)
            if inner_msg_tag == 'result':
                inner_inner_msg_tag, inner_inner_msg_args = inner_msg_args
                if inner_inner_msg_tag == 'continue':
                    return (('run', ('start', ())), ('continue', inner_inner_msg_args))
                elif inner_inner_msg_tag == 'break':
                    return (('end', ()), ('result', inner_inner_msg_args))
                else:
                    assert False, "Bad message: "+str(inner_inner_msg_tag)
            elif inner_msg_tag in ['continue', 'other']:
                return (('run', inner_state), (inner_msg_tag, inner_msg_args))
            else:
                assert False, "Bad message: "+str(inner_msg_tag)
        else:
            assert False, "Bad state: "+str(state_tag)
    return impl

def autopass(machine):
    def impl(state, msg):
        while True:
            state, (msg_tag, msg_args) = machine(state, msg)
            if msg_tag == 'continue':
                msg = msg_args
                continue
            else:
                return state, (msg_tag, msg_args)
    return impl

def seq(a, b):
    def impl(state, msg):
        state_tag, state_args = state
        if state_tag == 'start':
            return (('run_a', ('start', ())), ('continue', msg))
        elif state_tag == 'run_a':
            inner_state = state_args
            inner_state, (inner_msg_tag, inner_msg_args) = a(inner_state, msg)
            if inner_msg_tag == 'result':
                return (('run_b', ('start', ())), ('continue', inner_msg_args))
            elif inner_msg_tag == 'return':
                return (('end', ()), ('result', inner_msg_args))
            elif inner_msg_tag in ['continue', 'other']:
                return (('run_a', inner_state), (inner_msg_tag, inner_msg_args))
            else:
                assert False, "Bad message: "+str(inner_msg_tag)
        elif state_tag == 'run_b':
            inner_state = state_args
            inner_state, inner_msg = b(inner_state, msg)
            return (('run_b', inner_state), inner_msg)
        else:
            assert False, "Bad state: "+str(state_tag)
    return impl

def seqn(machines):
    result = machines.pop()
    while machines:
        result = seq(machines.pop(), result)
    return result

def do(fn):
    def impl(state, msg):
        assert state == ('start', ()), "Bad state"
        return (('end', ()), ('result', fn(*msg)))
    return impl

    
def other(state, msg):
    state_tag, state_args = state
    if state_tag == 'start':
        return (('awaiting', ()), ('other', msg))
    elif state_tag == 'awaiting':
        return (('end', ()), ('result', msg))
    else:
        assert False, "Bad state"

def if_then_else(then, els):
    def impl(state, msg):
        state_tag, state_args = state
        if state_tag == 'start':
            rest, cond = msg
            if cond:
                return ('call_then', ('start', ())), ('continue', rest)
            else:
                return ('call_els', ('start', ())), ('continue', rest)
        elif state_tag == 'call_then':
            inner_state = state_args
            inner_state, inner_msg = then(inner_state, msg)
            return ('call_then', inner_state), inner_msg
        elif state_tag == 'call_els':
            inner_state = state_args
            inner_state, inner_msg = els(inner_state, msg)
            return ('call_els', inner_state), inner_msg
        else:
            assert False, "Bad state: "+str(state_tag)
    return impl



def string_iter_equals_body(state, msg):
    state_tag, state_args = state
    if state_tag == 'start':
        str, offset, iter = msg
        return (0, (str, offset)), ('other', ('next', iter))
    elif state_tag == 0:
        str, offset = state_args
        iter, has_next = msg
        if len(str) == offset and not has_next:
            return (('end', ()), ('break', True))
        elif len(str) == offset or not has_next:
            return (('end', ()), ('break', False))
        else:
            return ((1, (str, offset)), ('other', ('iter_clone', iter)))
    elif state_tag == 1:
        str, offset = state_args
        iter, char = msg
        if char == str[offset]:
            return (('end', ()), ('continue', (str, offset + 1, iter)))
        else:
            return (('end', ()), ('break', False))
    else:
        assert False, "Bad state: "+str(state_tag)

string_iter_equals_body = seqn([
    do(lambda str, offset, iter: ((str, 0), ('next', iter))),
    smuggle(other),
    do(lambda str_offset, iter_res: ((*str_offset, iter_res[0]), iter_res[1])),
    if_then_else(
        # If has next.
        seqn([
            do(lambda str, offset, iter: ((str, offset), ('iter_clone', iter))),
            smuggle(other),
            do(lambda str, offset, clone_res: (str, offset, *clone_res)),
            do(lambda str, offset, iter, char: ((str, offset, iter), str[offset] == char)),
            if_then_else(
                # Chars equal.
                do(lambda str, offset, iter: ('continue', (str, offset + 1, iter))),
                # Chars not equal.
                do(lambda str, offset, iter: ('break', False)),
            ),
        ]),
        # If no next.
        do(lambda str, offset, iter: ('break', False)),
    )
])

string_iter_equals = seq(do(lambda str, iter: (str, 0, iter)), for_loop(string_iter_equals_body))

@do
def string_iter_next(str, offset):
    if len(str) == offset:
        return ('end', ()), ('result', False)
    else:
        return (str, offset + 1), ('result', True)

@do
def string_iter_clone(str, offset):
    return (str, offset), ('result', str[offset])   

# def string_iter_equals_inverse_handler(state, msg):
#     state_tag, state_args = state
#     if state_tag == 'start':
#         msg_tag, msg_args = msg
#         if msg_tag == 'next':
#             iter = msg_args
#             return (('call_inner', (('start', ()), iter)), ('pass', ()))
#         else:
#             assert False, "Bad message"
#     elif state_tag == 'call_inner':
#         inner_state, inner_msg = state_args
#         inner_state, (inner_msg_tag, inner_msg_args) = string_iter_equals(inner_state, inner_msg)


string_iter_equals_inverse_handler = seq(
    do(lambda tag, args: (tag == 'next', (tag, args))),
    if_then_else(
        
        do(lambda str, iter: (str, 0, iter)),
        for_loop(string_iter_equals_body)
    )
)


# def string_iter_equals_inverse(state, msg):
#     state_tag, state_args = state
#     if state_tag == 'start':
#         str = msg
#         iter = (str, 0)
#         return ('call_inner', (('start', ()), (str, iter))), ('pass', ())
#     elif state_tag == 'call_inner':
#         inner_state, inner_msg = state_args
#         inner_state, (inner_msg_tag, inner_msg_args) = string_iter_equals(inner_state, inner_msg)
#         if inner_msg_tag == 'result':
#             return (('end', ()), ('result', inner_msg_args))
#         elif inner_msg_tag == 'next':

#             return (('paused_inner', inner_state), inner_msg_args)
#         else:
#             assert False, "Bad message"
#     elif state_tag == 'paused_inner':
#         if inner_msg_tag == 'break':
#             return (('end', ()), ('result', inner_msg_args))
#         elif inner_msg_tag == 'continue':
#             return (('call_inner', (inner_state, ('next', inner_msg_args))), ('pass', ()))
#         elif inner_msg_tag == 'other':
#             return (('paused_inner', inner_state), inner_msg_args)
#         else:
#     elif state_tag == 0:
#         str, offset = state_args

def assertTranscript(test, fn, transcript):
    state = ('start', ())
    while transcript:
        (input, expected_output) = transcript.pop(0)
        state, actual_output = fn(state, input)
        test.assertEqual(actual_output, expected_output)


class TestStringIterEquals(unittest.TestCase):
    def test_success(self):
        transcript = [
            (('foo', 'iter'), ('other', ('next', 'iter'))),
            (('iter', True), ('other', ('iter_clone', 'iter'))),
            (('iter', 'f'), ('other', ('next', 'iter'))),
            (('iter', True), ('other', ('iter_clone', 'iter'))),
            (('iter', 'o'), ('other', ('next', 'iter'))),
            (('iter', True), ('other', ('iter_clone', 'iter'))),
            (('iter', 'o'), ('other', ('next', 'iter'))),
            (('iter', False), ('result', True))
        ]
        assertTranscript(self, autopass(string_iter_equals), transcript)
        
    def test_iter_shorter_than_string(self):
        transcript = [
            (('foo', 'iter'), ('other', ('next', 'iter'))),
            (('iter', True), ('other', ('iter_clone', 'iter'))),
            (('iter', 'f'), ('other', ('next', 'iter'))),
            (('iter', True), ('other', ('iter_clone', 'iter'))),
            (('iter', 'o'), ('other', ('next', 'iter'))),
            (('iter', False), ('result', False))
        ]
        assertTranscript(self, autopass(string_iter_equals), transcript)

    def test_string_shorter_than_iter(self):
        transcript = [
            (('f', 'iter'), ('other', ('next', 'iter'))),
            (('iter', True), ('other', ('iter_clone', 'iter'))),
            (('iter', 'f'), ('other', ('next', 'iter'))),
            (('iter', True), ('result', False))
        ]
        assertTranscript(self, autopass(string_iter_equals), transcript)

    def test_char_mismatch(self):
        transcript = [
            (('foo', 'iter'), ('other', ('next', 'iter'))),
            (('iter', True), ('other', ('iter_clone', 'iter'))),
            (('iter', 'f'), ('other', ('next', 'iter'))),
            (('iter', True), ('other', ('iter_clone', 'iter'))),
            (('iter', 'r'), ('result', False))
        ]
        assertTranscript(self, autopass(string_iter_equals), transcript)


def run_tests():
    """Run all tests and return the test suite."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add test cases to suite
    suite.addTests(loader.loadTestsFromTestCase(TestStringIterEquals))
    
    return suite



if __name__ == '__main__':
    # Run tests with verbose output
    runner = unittest.TextTestRunner(verbosity=2)
    suite = run_tests()
    result = runner.run(suite)
    
    # Exit with appropriate code
    sys.exit(not result.wasSuccessful())
