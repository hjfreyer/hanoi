from dataclasses import dataclass
from functools import wraps
from typing import Any, Callable, Literal, Protocol
import unittest
from beartype import beartype

from exp2 import *

StrIterState = tuple[Literal["start"]] | tuple[Literal["ready"], tuple[str, int]]


def str_iter(state: StrIterState, msg: Any) -> Result:
    if state[0] == "start":
        s = msg
        return Result("result", (), ("ready", (s, -1)))
    elif state[0] == "ready":
        iter = state[1]
        if msg[0] == "next":
            return str_iter_next(iter[0], iter[1])
        elif msg[0] == "clone":
            return str_iter_clone(iter[0], iter[1])
        else:
            assert False, "Bad msg: " + str(msg)


def str_iter_next(s: str, offset: int) -> Result:
    offset += 1

    if offset == len(s):
        return Result("result", False, ("ready", (s, offset)))
    else:
        return Result("result", True, ("ready", (s, offset)))


def str_iter_clone(s: str, offset: int) -> Result:
    return Result("result", s[offset], ("ready", (s, offset)))


def str_iter_equals_body(state: tuple[str, Any], msg: Any) -> Result:
    if state[0] == "start":
        s, offset = msg
        return Result("iter", ("next",), ("iter_next_cb", (s, offset)))
    elif state[0] == "iter_next_cb":
        s, offset = state[1]
        iter_has_next = msg
        str_has_next = offset < len(s)

        if not iter_has_next and not str_has_next:
            return Result("break", True, ("end", None))
        elif not iter_has_next or not str_has_next:
            return Result("break", False, ("end", None))
        else:
            return Result("iter", ("clone",), ("iter_clone_cb", (s, offset)))
    elif state[0] == "iter_clone_cb":
        s, offset = state[1]
        iter_char = msg
        str_char = s[offset]
        if iter_char == str_char:
            return Result("next_loop", (s, offset + 1), ("end", None))
        else:
            return Result("break", False, ("end", None))
    else:
        assert False, "Bad state: " + state[0]


def str_iter_equals_preamble(state: tuple[str, Any], msg: Any) -> Result:
    assert state[0] == "start", "Bad state: " + state[0]
    s = msg
    return Result("result", (s, 0), ("end", None))


str_iter_equals = Bound(
    str_iter_equals_preamble,
    {
        "result": AndThen(ForLoop(str_iter_equals_body)),
    },
)


def str_iter_equals_inverse_preamble(
    state: tuple[Literal["start"]] | tuple[Literal["await_init"], str],
    msg: Any,
) -> Result:
    if state[0] == "start":
        s = msg
        return Result("iter", s, ("await_init", s))
    elif state[0] == "await_init":
        s = state[1]
        return Result("result", s, ("end", None))


string_iter_equals_inverse = Bound(
    Bound(
        str_iter_equals_inverse_preamble,
        {
            "result": AndThen(
                Bound(
                    str_iter_equals,
                    {
                        "continue": PassThroughHandler(),
                        "iter": PassThroughHandler(),
                        "result": PassThroughHandler(),
                    },
                )
            ),
            "iter": PassThroughHandler(),
            "continue": PassThroughHandler(),
        },
    ),
    {
        "iter": ImplHandler(str_iter),
        "result": PassThroughHandler(),
        "continue": PassThroughHandler(),
    },
)


def emit_twice(state: tuple[str, Any], msg: Any) -> Result:
    if state[0] == "start":
        return Result("get_items", None, ("await_items", msg))
    elif state[0] == "await_items":
        prev_msg = state[1]
        return Result("continue", prev_msg, ("at", (-1, msg)))
    elif state[0] == "at":
        at, items = state[1]
        if msg[0] == "next":
            at += 1
            return Result("result", at < 2, ("at", (at, items)))
        elif msg[0] == "clone":
            return Result("result", items[at], state)
        else:
            assert False, "Bad msg: " + str(msg)
    else:
        assert False, "Bad state: " + str(state)


def result_second(state: tuple[str, Any], msg: Any) -> Result:
    if state[0] == "start":
        return Result("iter", ("next",), ("wait1", None))
    elif state[0] == "wait1":
        return Result("iter", ("next",), ("wait2", None))
    elif state[0] == "wait2":
        return Result("iter", ("clone",), ("wait3", None))
    elif state[0] == "wait3":
        return Result("result", msg, ("end", None))
    else:
        assert False, "Bad state: " + str(state)


twice_test = Bound(
    result_second,
    {
        "iter": ImplHandler(
            Bound(
                emit_twice,
                {
                    "get_items": ImplHandler(transformer(lambda x: ("foo", "bar"))),
                    "continue": PassThroughHandler(),
                    "result": PassThroughHandler(),
                },
            )
        ),
        "result": PassThroughHandler(),
    },
)


def assertTranscript(
    test: unittest.TestCase, machine: Any, transcript: list[tuple[Any, str, Any]]
):
    state = ("start",)
    while transcript:
        (input, result_tag, result_args) = transcript.pop(0)
        result = machine(state, input)
        while result.action == "continue":
            state, input = result.resume_state, result.action_args
            result = machine(state, input)
        test.assertEqual(result.action, result_tag)
        test.assertEqual(result.action_args, result_args)
        state = result.resume_state


class TestMisc(unittest.TestCase):

    def test_emit_twice(self):
        transcript: list[tuple[Any, str, Any]] = [
            (("next",), "get_items", None),
            (("foo", "bar"), "result", True),
            (("clone",), "result", "foo"),
            (("next",), "result", True),
            (("clone",), "result", "bar"),
            (("next",), "result", False),
        ]
        assertTranscript(self, emit_twice, transcript)

    def test_result_second(self):
        transcript: list[tuple[Any, str, Any]] = [
            (None, "iter", ("next",)),
            (True, "iter", ("next",)),
            (True, "iter", ("clone",)),
            ("foo", "result", "foo"),
        ]
        assertTranscript(self, result_second, transcript)

    def test_twice(self):
        transcript: list[tuple[Any, str, Any]] = [
            (None, "result", "bar"),
        ]
        assertTranscript(self, twice_test, transcript)


class TestStringIter(unittest.TestCase):
    def test_next(self):
        transcript: list[tuple[Any, str, Any]] = [
            ("foo", "result", ()),
            (("next",), "result", True),
        ]
        assertTranscript(self, str_iter, transcript)

    def test_clone(self):
        transcript: list[tuple[Any, str, Any]] = [
            ("foo", "result", ()),
            (("next",), "result", True),
            (("clone",), "result", "f"),
        ]
        assertTranscript(self, str_iter, transcript)


class TestStringIterEquals(unittest.TestCase):

    def test_success(self):
        transcript: list[tuple[Any, str, Any]] = [
            ("foo", "iter", ("next",)),
            (True, "iter", ("clone",)),
            ("f", "iter", ("next",)),
            (True, "iter", ("clone",)),
            ("o", "iter", ("next",)),
            (True, "iter", ("clone",)),
            ("o", "iter", ("next",)),
            (False, "result", True),
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_iter_shorter_than_string(self):
        transcript: list[tuple[Any, str, Any]] = [
            ("foo", "iter", ("next",)),
            (True, "iter", ("clone",)),
            ("f", "iter", ("next",)),
            (True, "iter", ("clone",)),
            ("o", "iter", ("next",)),
            (False, "result", False),
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_string_shorter_than_iter(self):
        transcript: list[tuple[Any, str, Any]] = [
            ("f", "iter", ("next",)),
            (True, "iter", ("clone",)),
            ("f", "iter", ("next",)),
            (True, "result", False),
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_char_mismatch(self):
        transcript: list[tuple[Any, str, Any]] = [
            ("foo", "iter", ("next",)),
            (True, "iter", ("clone",)),
            ("f", "iter", ("next",)),
            (True, "iter", ("clone",)),
            ("r", "result", False),
        ]
        assertTranscript(self, str_iter_equals, transcript)

    def test_inverse(self):
        transcript: list[tuple[Any, str, Any]] = [("foo", "result", True)]
        assertTranscript(self, string_iter_equals_inverse, transcript)


@beartype
def char_iter(
    state: (
        tuple[Literal["start"]]
        | tuple[Literal["await_next"]]
        | tuple[Literal["await_clone"]]
    ),
    msg: Any,
) -> Result:
    if state[0] == "start":
        assert msg == ("next",), "Bad msg: " + str(msg)
        return Result("iter", ("next",), ("await_next",))
    elif state[0] == "await_next":
        if msg:
            return Result("iter", ("clone",), ("await_clone",))
        else:
            return Result("result", ("none",), ("end",))
    elif state[0] == "await_clone":
        return Result("result", ("some", msg), ("start",))

def char_iter_from_string_preamble(state: Any, msg: Any) -> Result:
    if state[0] == "start":
        return Result("str_iter", msg, ("await_init",))
    elif state[0] == "await_init":
        return Result("result", (), ("proxy_char_iter",))
    elif state[0] == "proxy_char_iter":
        return Result("char_iter", msg, ("await_char_iter",))
    elif state[0] == "await_char_iter":
        return Result("result", msg, ("proxy_char_iter",))
    else:
        assert False, "Bad state: " + str(state)


char_iter_from_string = Bound(
    Bound(
        char_iter_from_string_preamble,
        {
            "result": PassThroughHandler(),
            "continue": PassThroughHandler(),
            "str_iter": PassThroughHandler(),
            "char_iter": ImplHandler(
                Bound(
                    char_iter,
                    {
                        "result": PassThroughHandler(),
                        "continue": PassThroughHandler(),
                        "iter": PassThroughHandler("str_iter"),
                    },
                )
            ),
        },
    ),
    {
        "result": PassThroughHandler(),
        "continue": PassThroughHandler(),
        "str_iter": ImplHandler(str_iter),
    },
)


class TestCharIter(unittest.TestCase):
    def test_from_string(self):
        transcript: list[tuple[Any, str, Any]] = [
            ("foo", "result", ()),
            (("next",), "result", ("some", "f")),
            (("next",), "result", ("some", "o")),
            (("next",), "result", ("some", "o")),
            (("next",), "result", ("none",)),
        ]
        assertTranscript(self, char_iter_from_string, transcript)


type SSVState = (
    tuple[Literal["start"]]
    | tuple[Literal["field_start"]]
    | tuple[Literal["await_next"]]
    | tuple[Literal["in_field"], str]
    | tuple[Literal["almost_finished"]]
)


@beartype
def space_separated_values(state: SSVState, msg: Any) -> Result:
    if state[0] == "start":
        assert msg == ("next",), "Bad msg: " + str(msg)
        return Result("result", True, ("field_start",))
    elif state[0] == "field_start":
        assert msg == ("inner_next",), "Bad msg: " + str(msg)
        return Result("iter", ("next",), ("await_next",))
    elif state[0] == "await_next":
        if msg[0] == "some":
            char = msg[1]
            if char == " ":
                return Result("result", False, ("start",))
            else:
                return Result("result", True, ("in_field", char))
        elif msg[0] == "none":
            return Result("result", False, ("almost_finished",))
    elif state[0] == "in_field":
        char = state[1]
        if msg[0] == "inner_next":
            return Result("iter", ("next",), ("await_next",))
        elif msg[0] == "inner_clone":
            return Result("result", char, state)
        else:
            assert False, "Bad msg: " + str(msg)
    elif state[0] == "almost_finished":
        assert msg[0] == "next", "Bad msg: " + str(msg)
        return Result("result", False, ("end",))
    assert False, "Bad state: " + str(state)


def space_separated_values_for_string_impl(state: Any, msg: Any) -> Result:
    if state[0] == "start":
        return Result("iter", msg, ("await_init",))
    elif state[0] == "await_init":
        return Result("result", (), ("proxy",))
    elif state[0] == "proxy":
        return Result("ssv", msg, ("await_ssv",))
    elif state[0] == "await_ssv":
        return Result("result", msg, ("proxy",))
    else:
        assert False, "Bad state: " + str(state)


space_separated_values_for_string = Bound(
    Bound(
        space_separated_values_for_string_impl,
        {
            "result": PassThroughHandler(),
            "continue": PassThroughHandler(),
            "iter": PassThroughHandler(),
            "ssv": ImplHandler(space_separated_values),
        },
    ),
    {
        "result": PassThroughHandler(),
        "continue": PassThroughHandler(),
        "iter": ImplHandler(char_iter_from_string),
    },
)


class TestSpaceSeparatedValues(unittest.TestCase):
    def test_empty(self):
        transcript: list[tuple[Any, str, Any]] = [
            ("", "result", ()),
            (("next",), "result", True),
            (("inner_next",), "result", False),
            # (("next",), "result", False),
        ]
        assertTranscript(self, space_separated_values_for_string, transcript)

    def test_one_field(self):
        transcript: list[tuple[Any, str, Any]] = [
            ("foo", "result", ()),
            (("next",), "result", True),
            (("inner_next",), "result", True),
            (("inner_clone",), "result", "f"),
            (("inner_next",), "result", True),
            (("inner_clone",), "result", "o"),
            (("inner_next",), "result", True),
            (("inner_next",), "result", False),
            (("next",), "result", False),
        ]
        assertTranscript(self, space_separated_values_for_string, transcript)

    def test_double_field(self):
        transcript: list[tuple[Any, str, Any]] = [
            ("foo b", "result", ()),
            (("next",), "result", True),
            (("inner_next",), "result", True),
            (("inner_clone",), "result", "f"),
            (("inner_next",), "result", True),
            (("inner_clone",), "result", "o"),
            (("inner_next",), "result", True),
            (("inner_clone",), "result", "o"),
            (("inner_next",), "result", False),
            (("next",), "result", True),
            (("inner_next",), "result", True),
            (("inner_clone",), "result", "b"),
            (("inner_next",), "result", False),
            (("next",), "result", False),
        ]
        assertTranscript(self, space_separated_values_for_string, transcript)

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


if __name__ == "__main__":
    unittest.main()
