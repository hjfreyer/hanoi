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


StrIter = tuple[str, int]


@beartype
def str_iter_equals_body(
    state: (
        tuple[Literal["start"]]
        | tuple[Literal["iter_next_cb"], StrIter]
        | tuple[Literal["iter_clone_cb"], StrIter]
    ),
    msg: Any,
) -> Result:
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
    test: unittest.TestCase,
    machine: Any,
    transcript: list[tuple[Any, str, Any]],
    init=("start",),
):
    state = init
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


@transformer
def str_iter2_init(s: str) -> Any:
    return (s, -1)


@beartype
def str_iter2(state: tuple[str, int], msg: Any) -> Result:
    s, offset = state
    if msg[0] == "next":
        offset += 1
        if offset == len(s):
            return Result("result", False, (s, offset))
        else:
            return Result("result", True, (s, offset))
    elif msg[0] == "clone":
        return Result("result", s[offset], state)
    else:
        assert False, "Bad msg: " + str(msg)


# (("start",), "foo") string_iter_equals_inverse2
# ("foo", (("start",), "foo")) (id, str_iter2_init)
# ("foo", iter:=("foo", -1)) string_iter_equals_inverse2_line2
# (iter, (("start",), "foo")) str_iter_equals
# - raises "iter"
#   - (iter, ("iter", "next")) string_iter_equals_inverse2_line3_handler
#     - (iter, "next") str_iter2
#     - ()

# def string_iter_equals_inverse2_1(state: Any, msg: Any) -> Result:


@beartype
def string_iter_equals_inverse2_bound(
    state: (
        tuple[Literal["start"], tuple[tuple[str, int], Any]]
        | tuple[Literal["call_iter"], tuple[tuple[str, int], Any]]
    ),
    msg: Any,
) -> Result:
    if state[0] == "start":
        (iter_state, str_iter_equals_state) = state[1]
        result = str_iter_equals(str_iter_equals_state, msg)
        if result.action == "iter":
            return Result(
                "continue", msg, ("call_iter", (iter_state, result.resume_state))
            )
        elif result.action == "result":
            return Result("result", result.action_args, ("end",))
        elif result.action == "continue":
            return Result("continue", msg, ("start", (iter_state, result.resume_state)))
        else:
            assert False, "Bad result: " + str(result)
    elif state[0] == "call_iter":
        iter_state, iter_equals_resume_state = state[1]
        result = str_iter2(iter_state, msg)
        if result.action == "result":
            return Result(
                "result",
                result.action_args,
                ("start", (result.resume_state, iter_equals_resume_state)),
            )
        elif result.action == "continue":
            return Result(
                "continue",
                msg,
                ("call_iter", (result.resume_state, iter_equals_resume_state)),
            )
        else:
            assert False, "Bad result: " + str(result)
    else:
        assert False, "Bad state: " + state[0]


@dataclass
class SeqHandler:
    inner: Machine

    def handle(
        self, handler_name: str, handler_state: Any, msg: Any
    ) -> HandlerResume | HandlerContinue:
        assert handler_name == "result", "Bad handler name: " + handler_name
        result = self.inner(handler_state, msg)
        return HandlerContinue(
            "continue", result.action, result.action_args, result.resume_state
        )


@dataclass
class ResultHandler:
    def handle(
        self, handler_name: str, handler_state: Any, msg: Any
    ) -> HandlerResume | HandlerContinue | HandlerResult:
        assert handler_name == "result", "Bad handler name: " + handler_name
        return HandlerResult("result", (handler_state, msg))


@transformer
@beartype
def string_iter_equals_inverse2_line2(msg: tuple[str, StrIter]) -> Any:
    return (msg[1], ("start",), msg[0])


class ThingyHandler:
    def handle(
        self, handler_name: str, handler_state: Any, msg: Any
    ) -> HandlerResume | HandlerContinue | HandlerResult:
        print("ThingyHandler", handler_name, handler_state, msg)


string_iter_equals_inverse2 = Bound(
    Bound(
        transformer(lambda s: (s, ("start",), s)),
        {
            "result": AndThen(Call(str_iter2_init, ResultHandler())),
            "continue": PassThroughHandler(),
        },
    ),
    {
        "continue": PassThroughHandler(),
        "result": AndThen(
            Bound(
                string_iter_equals_inverse2_line2,
                {
                    "result": AndThen(Call(str_iter_equals, ThingyHandler())),
                    "continue": PassThroughHandler(),
                },
            )
        ),
    },
)


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

    def test_inverse2_bound(self):
        transcript: list[tuple[Any, str, Any]] = [("foo", "result", True)]
        assertTranscript(self, string_iter_equals_inverse2, transcript)


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


@transformer
def char_iter_from_string2(s: str) -> Any:
    return char_iter_from_string(("start",), s)


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


@dataclass
class Bundle:
    machines: dict[str, Machine]

    def __call__(self, state: Any, msg: Any) -> Result:
        if state[0] == "start":
            return Result(
                "continue", msg, ("started", {k: ("start",) for k in self.machines})
            )
        elif state[0] == "started":
            machine_states = state[1]
            machine_name, machine_msg = msg
            machine_state = machine_states[machine_name]
            machine = self.machines[machine_name]
            result = machine(machine_state, machine_msg)
            machine_states |= {machine_name: result.resume_state}
            return Result(
                result.action, result.action_args, ("started", machine_states)
            )
        else:
            assert False, "Bad state: " + str(state)


space_separated_values_for_string_bundle = Bundle(
    {
        "char_iter": char_iter_from_string,
        "ssv": space_separated_values,
    }
)


# def space_separated_values_for_string(state: Any, msg: Any) -> Result:
#     if state[0] == "start":
#         s = msg
#         return space_separated_values_for_string_bundle(state, ("char_iter", s))
#     elif state[0] == "started":
#         ssv_state, iter_state = state[1]
#         ssv_result = space_separated_values(ssv_state, msg)
#         if ssv_result.action == "iter":

#     else:
#         assert False, "Bad state: " + str(state)


# space_separated_values_for_string = Bound(
#     Bound(
#         space_separated_values_for_string_impl,
#         {
#             "result": PassThroughHandler(),
#             "continue": PassThroughHandler(),
#             "iter": PassThroughHandler(),
#             "ssv": ImplHandler(space_separated_values),
#         },
#     ),
#     {
#         "result": PassThroughHandler(),
#         "continue": PassThroughHandler(),
#         "iter": ImplHandler(char_iter_from_string),
#     },
# )


# class TestSpaceSeparatedValues(unittest.TestCase):
#     def test_empty(self):
#         transcript: list[tuple[Any, str, Any]] = [
#             ("", "result", ()),
#             (("next",), "result", True),
#             (("inner_next",), "result", False),
#             # (("next",), "result", False),
#         ]
#         assertTranscript(self, space_separated_values_for_string, transcript)

#     def test_one_field(self):
#         transcript: list[tuple[Any, str, Any]] = [
#             ("foo", "result", ()),
#             (("next",), "result", True),
#             (("inner_next",), "result", True),
#             (("inner_clone",), "result", "f"),
#             (("inner_next",), "result", True),
#             (("inner_clone",), "result", "o"),
#             (("inner_next",), "result", True),
#             (("inner_next",), "result", False),
#             (("next",), "result", False),
#         ]
#         assertTranscript(self, space_separated_values_for_string, transcript)

#     def test_double_field(self):
#         transcript: list[tuple[Any, str, Any]] = [
#             ("foo b", "result", ()),
#             (("next",), "result", True),
#             (("inner_next",), "result", True),
#             (("inner_clone",), "result", "f"),
#             (("inner_next",), "result", True),
#             (("inner_clone",), "result", "o"),
#             (("inner_next",), "result", True),
#             (("inner_clone",), "result", "o"),
#             (("inner_next",), "result", False),
#             (("next",), "result", True),
#             (("inner_next",), "result", True),
#             (("inner_clone",), "result", "b"),
#             (("inner_next",), "result", False),
#             (("next",), "result", False),
#         ]
#         assertTranscript(self, space_separated_values_for_string, transcript)

#     def test_empty_final_field(self):
#         transcript: list[tuple[Any, str, Any]] = [
#             ("f ", "result", ()),
#             (("next",), "result", True),
#             (("inner_next",), "result", True),
#             (("inner_clone",), "result", "f"),
#             (("inner_next",), "result", False),
#             (("next",), "result", True),
#             (("inner_next",), "result", False),
#             (("next",), "result", False),
#         ]
#         assertTranscript(self, space_separated_values_for_string, transcript)

if __name__ == "__main__":
    unittest.main()
