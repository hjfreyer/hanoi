#!/usr/bin/env python3
"""
Sample Python unittest module for experiment testing.
This module demonstrates proper unittest structure and patterns.
"""

from dataclasses import dataclass
from functools import wraps
import unittest
import sys
from typing import Callable, Literal, Protocol, Tuple, Any, Optional, Self, override

Value = str | int | float | bool | tuple['Value', ...]

class Stack:
    def __init__(self, items: tuple[Value, ...]):
        self.items : tuple[Value, ...] = items

    def push(self, item: Value) -> Self:
        return self.__class__((item,) + self.items)
    
    def pop[T : Value](self) -> tuple[Self, T]:
        return self.__class__(self.items[1:]), self.items[0] # pyright: ignore[reportReturnType]
        
    def move(self, idx: int) -> Self:
        return self.__class__((self.items[idx], ) + self.items[:idx] + self.items[idx+1:])

    def copy(self, idx: int) -> Self:
        return self.__class__((self.items[idx], ) + self.items)

    def drop(self, idx: int) -> Self:
        return self.__class__(self.items[:idx] + self.items[idx+1:])

    def __str__(self) -> str:
        return str(self.items)

@dataclass
class Locals:
    names: tuple[str | None, ...] = ()
    unreachable: bool = False

    def push_named(self, name: str) -> Self:
        assert not self.unreachable, "Unreachable locals"
        return self.__class__((name,) + self.names)
    
    def push_unnamed(self) -> Self:
        assert not self.unreachable, "Unreachable locals"
        return self.__class__((None,) + self.names)
    
    def pop_unnamed(self) -> Self:
        assert not self.unreachable, "Unreachable locals"
        assert self.names[0] is None, "Variable was named: "+self.names[0]
        return self.__class__(self.names[1:])

    @override
    def __str__(self) -> str:
        return str(self.names)

    def compatible_with(self, other: Self) -> bool:
        if self.unreachable or other.unreachable:
            return True
        return self.names == other.names

    def merge(self, other: Self) -> Self:
        assert self.compatible_with(other), "Must be compatible: "+str(self)+" != "+str(other)
        if self.unreachable:
            return other
        return self

    @staticmethod
    def make_unreachable() -> "Locals":
        return Locals(names=(), unreachable=True)

    @staticmethod
    def simple(locals : 'Locals') -> dict[str, 'Locals']:
        return {'result':locals, 'return':Locals.make_unreachable()}

    def index(self, name: str) -> int:
        assert not self.unreachable, "Unreachable locals"
        assert name in self.names, "Name not found: "+name
        return self.names.index(name)

    def move(self, idx: int) -> Self:
        assert not self.unreachable, "Unreachable locals"
        return self.__class__((None, ) + self.names[:idx] + self.names[idx+1:])

    def drop(self, idx: int) -> Self:
        assert not self.unreachable, "Unreachable locals"
        return self.__class__(self.names[:idx] + self.names[idx+1:])

class Machine(Protocol):
    def __call__(self, stack: "Stack") -> "Stack": ...

class MachineBuilder(Protocol):
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]: ...

@dataclass
class DropIdx(MachineBuilder):
    idx : int

    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        def run(stack: Stack) -> Stack:
            stack, state = stack.pop()
            assert state == ('start', ()), "Bad state: "+str(state)
            stack = stack.drop(self.idx)
            stack = stack.push(('end', ()))
            stack = stack.push(('result', ()))
            return stack
        return Locals.simple(locals.drop(self.idx)), run

@dataclass
class Drop(MachineBuilder):
    name : str

    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        return DropIdx(locals.index(self.name))(locals)

def transformer(f: Callable[[Value], Value]) -> MachineBuilder:
    def compile(locals: Locals) -> tuple[dict[str, Locals], Machine]:
        @wraps(f)
        def run(stack: Stack) -> Stack:
            stack, state = stack.pop()
            assert state == ('start', ()), "Bad state"
            stack, value = stack.pop()
            stack = stack.push(f(value))
            stack = stack.push(('end', ()))
            stack = stack.push(('result', ()))
            return stack
        return {'result': locals.pop_unnamed().push_unnamed(), 'return': Locals.make_unreachable()}, run
    return compile
    
def smuggle(machine):
    @wraps(machine)
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

@dataclass
class ForLoop(MachineBuilder):
    body : MachineBuilder

    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:

        return self.machine(locals)
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

def autopass(machine : Machine) -> Machine:
    def impl(stack: Stack) -> Stack:
        while True:
            stack = machine(stack)
            stack, (action_tag, action_args) = stack.pop()
            if action_tag == 'continue':
                continue
            else:
                stack = stack.push((action_tag, action_args))
                return stack
    return impl

@dataclass
class Compose(MachineBuilder):
    a : MachineBuilder
    b : MachineBuilder

    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        a_locals, a_run = self.a(locals)
        b_locals, b_run = self.b(a_locals['result'])

        assert a_locals['return'].compatible_with(b_locals['return']), "A and B must have the same return: "+str(a_locals['return'])+" != "+str(b_locals['return'])

        def run_b(stack: Stack) -> Stack:
            stack = b_run(stack)
            stack, action = stack.pop()
            stack, state = stack.pop()
            stack = stack.push(('run_b', state))
            stack = stack.push(action)
            return stack

        def run_a(stack: Stack) -> Stack:
            stack = a_run(stack)
            stack, (action_tag, action_args) = stack.pop() # pyright: ignore[reportGeneralTypeIssues]
            stack, inner_state = stack.pop()
            if action_tag == 'result':
                stack = stack.push(('start', ()))
                return run_b(stack)
            elif action_tag == 'return':
                stack = stack.push(('end', ()))
                stack = stack.push(('result', ()))
                return stack
            elif action_tag in ['continue', 'other']:
                stack = stack.push(('run_a', inner_state))
                stack = stack.push((action_tag, action_args))
                return stack
            else:
                assert False, "Bad message: "+str(action_tag)


        def run(stack: Stack) -> Stack:
            stack, (state_tag, state_args) = stack.pop()
            if state_tag == 'start':
                stack = stack.push(('start', ()))
                return run_a(stack)
            elif state_tag == 'run_a':
                inner_state = state_args
                stack = stack.push(inner_state)
                return run_a(stack)
            elif state_tag == 'run_b':
                inner_state = state_args
                stack = stack.push(inner_state)
                return run_b(stack)
            else:
                assert False, "Bad state: "+str(state_tag)

        return b_locals, run


def seqn(builders : list[MachineBuilder]) -> MachineBuilder:
    result = builders.pop()
    while builders:
        result = Compose(builders.pop(), result)
    return result

def do(fn):
    def impl(state, msg):
        assert state == ('start', ()), "Bad state"
        return (('end', ()), ('result', fn(msg)))
    return impl

def dot(fn):
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

@dataclass
class IfThenElse(MachineBuilder):
    then : MachineBuilder
    els : MachineBuilder

    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        locals = locals.pop_unnamed()
        then_locals, then_machine = self.then(locals)
        els_locals, els_machine = self.els(locals)

        print("then: "+str(self.then))
        print("els: "+str(self.els))
        result_locals = then_locals['result'].merge(els_locals['result'])
        return_locals = then_locals['return'].merge(els_locals['return'])

        def run_then(stack: Stack) -> Stack:
            stack = then_machine(stack)
            stack, action = stack.pop()
            stack, inner_state = stack.pop()
            stack = stack.push(('run_then', inner_state))
            stack = stack.push(action)
            return stack
        
        def run_els(stack: Stack) -> Stack:
            stack = els_machine(stack)
            stack, action = stack.pop()
            stack, inner_state = stack.pop()
            stack = stack.push(('run_else', inner_state))
            stack = stack.push(action)
            return stack

        def run(stack: Stack) -> Stack:
            stack, (state_tag, state_args) = stack.pop()
            if state_tag == 'start':
                stack, cond = stack.pop()
                if cond:
                    stack = stack.push(('start', ()))
                    return run_then(stack)
                else:
                    stack = stack.push(('start', ()))
                    return run_els(stack)
            elif state_tag == 'run_then':
                inner_state = state_args
                stack = stack.push(inner_state)
                return run_then(stack)
            elif state_tag == 'run_else':
                inner_state = state_args
                stack = stack.push(inner_state)
                return run_els(stack)
            else:
                assert False, "Bad state: "+str(state_tag)
        return {'result': result_locals, 'return': return_locals}, run



# def string_iter_equals_body(state, msg):
#     state_tag, state_args = state
#     if state_tag == 'start':
#         str, offset, iter = msg
#         return (0, (str, offset)), ('other', ('next', iter))
#     elif state_tag == 0:
#         str, offset = state_args
#         iter, has_next = msg
#         if len(str) == offset and not has_next:
#             return (('end', ()), ('break', True))
#         elif len(str) == offset or not has_next:
#             return (('end', ()), ('break', False))
#         else:
#             return ((1, (str, offset)), ('other', ('iter_clone', iter)))
#     elif state_tag == 1:
#         str, offset = state_args
#         iter, char = msg
#         if char == str[offset]:
#             return (('end', ()), ('continue', (str, offset + 1, iter)))
#         else:
#             return (('end', ()), ('break', False))
#     else:
#         assert False, "Bad state: "+str(state_tag)


@dataclass
class NameBinding:
    kind : Literal['name']
    name: str

    def transform(self, locals: Locals) -> Locals:
        return locals.pop_unnamed().push_named(self.name)

    def run(self, stack: Stack) -> Stack:
        return stack

    def test(self, value: Value) -> bool:
        return True

@dataclass
class LiteralBinding:
    kind : Literal['literal']
    value : Value

    def transform(self, locals: Locals) -> Locals:
        return locals.pop_unnamed()

    def run(self, stack: Stack) -> Stack:
        stack, value = stack.pop()
        assert value == self.value, "Expected "+str(self.value)+", got "+str(value)
        return stack

    def test(self, value: Value) -> bool:
        return value == self.value

@dataclass
class TupleBinding:
    kind : Literal['tuple']
    values : tuple['Binding', ...]

    def transform(self, locals: Locals) -> Locals:
        locals = locals.pop_unnamed()
        for binding in self.values:
            locals = locals.push_unnamed()
            locals = binding.transform(locals)
        return locals

    def run(self, stack: Stack) -> Stack:
        stack, value = stack.pop()
        assert isinstance(value, tuple), "Expected tuple, got "+str(value)
        assert len(value) == len(self.values), "Expected "+str(len(self.values))+" values, got "+str(len(value))
        for binding, value in zip(self.values, value):
            stack = stack.push(value)
            stack = binding.run(stack)
        return stack

    def test(self, value: Value) -> bool:
        assert isinstance(value, tuple), "Expected tuple, got "+str(value)
        assert len(value) == len(self.values), "Expected "+str(len(self.values))+" values, got "+str(len(value))
        for binding, value in zip(self.values, value):
            if not binding.test(value):
                return False
        return True

def name_binding(name : str) -> NameBinding:
    return NameBinding('name', name)

def literal_binding(value : Value) -> LiteralBinding:
    return LiteralBinding('literal', value)

def tuple_binding(values : tuple['Binding', ...]) -> TupleBinding:
    return TupleBinding('tuple', values)

Binding = NameBinding | LiteralBinding | TupleBinding

@dataclass
class Bind(MachineBuilder):
    binding : Binding

    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        def run(stack: Stack) -> Stack:
            stack, state = stack.pop()
            assert state == ('start', ()), "Bad state"
            stack = self.binding.run(stack)
            stack = stack.push(('end', ()))
            stack = stack.push(('result', ()))
            return stack
        return Locals.simple(self.binding.transform(locals)), run

@dataclass
class MoveIdx(MachineBuilder):
    idx : int
    
    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        def run(stack: Stack) -> Stack:
            stack, state = stack.pop()
            assert state == ('start', ()), "Bad state"
            stack = stack.move(self.idx)  # maybe wrong
            stack = stack.push(('end', ()))
            stack = stack.push(('result', ()))
            return stack
        return Locals.simple(locals.move(self.idx)), run

@dataclass
class Move(MachineBuilder):
    name : str

    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        index = locals.index(self.name)
        return MoveIdx(index)(locals)

@dataclass
class CopyIdx(MachineBuilder):
    idx : int
    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        def run(stack: Stack) -> Stack:
            stack, state = stack.pop()
            assert state == ('start', ()), "Bad state"
            stack = stack.copy(self.idx)
            stack = stack.push(('end', ()))
            stack = stack.push(('result', ()))
            return stack
        return Locals.simple(locals.push_unnamed()), run

@dataclass
class Copy(MachineBuilder):
    name : str
    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        index = locals.index(self.name)
        return CopyIdx(index)(locals)

@dataclass
class Push(MachineBuilder):
    value : Value

    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        def run(stack: Stack) -> Stack:
            stack, state = stack.pop()
            assert state == ('start', ()), "Bad state"
            stack = stack.push(self.value)
            stack = stack.push(('end', ()))
            stack = stack.push(('result', ()))
            return stack
        return Locals.simple(locals.push_unnamed()), run

@dataclass
class MakeTuple(MachineBuilder):
    size : int

    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        for _ in range(self.size):
            locals = locals.pop_unnamed()
        locals = locals.push_unnamed()

        def run(stack: Stack) -> Stack:
            stack, state = stack.pop()
            assert state == ('start', ()), "Bad state"
            values = []
            for _ in range(self.size):
                stack, value = stack.pop()
                values.append(value)
            stack = stack.push(tuple(reversed(values)))
            stack = stack.push(('end', ()))
            stack = stack.push(('result', ()))
            return stack
        return Locals.simple(locals), run

@dataclass
class Call(MachineBuilder):
    remote : Machine

    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        def run_remote(stack: Stack) -> Stack:
            stack = self.remote(stack)
            stack, (action_tag, action_args) = stack.pop()
            stack, inner_state = stack.pop()
            if action_tag == 'result':
                stack = stack.push(('end', ()))
                stack = stack.push(('result', ()))
                return stack
            elif action_tag == 'other':
                saved : list[Value] = []
                stack, request = stack.pop()
                for _ in range(len(locals.names) - 1):
                    stack, value = stack.pop()
                    saved.append(value)
                stack = stack.push(request)
                stack = stack.push(('paused', (tuple(saved), inner_state)))
                stack = stack.push(('other', ()))
                return stack
            else:
                assert False, "Bad action: "+str(action_tag)

        def run(stack: Stack) -> Stack:
            stack, (state_tag, state_args) = stack.pop()
            if state_tag == 'start':
                stack = stack.push(('start', ()))
                return run_remote(stack)
            elif state_tag == 'paused':
                saved, inner_state = state_args
                stack, response = stack.pop()
                for value in reversed(saved):
                    stack = stack.push(value)
                stack = stack.push(response)
                stack = stack.push(inner_state)
                return run_remote(stack)
            else:
                assert False, "Bad state: "+str(state_tag)

        return Locals.simple(locals), run

def compile_function(builder : MachineBuilder) -> Machine:
    locals = Locals(names=())
    locals = locals.push_unnamed()
    locals, machine = builder(locals)
    assert locals['result'].names == (None,), "Expected "+str(locals['result'].names)+" to be "+str((None,))
    return machine

simple_test = compile_function(seqn([
    Bind(tuple_binding(())),
    Push(1),
    Bind(name_binding('x')),
    Push(2),
    Bind(name_binding('y')),
    Copy('x'),
    Move('x'),
    Move('y'),
    MakeTuple(3),
]))

@dataclass
class OtherBuilder(MachineBuilder):
    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        def run(stack: Stack) -> Stack:
            stack, state = stack.pop()
            if state == ('start', ()):
                stack = stack.push(('awaiting', ()))
                stack = stack.push(('other', ()))
                return stack
            elif state == ('awaiting', ()):
                # The result is on the top of the stack.
                stack = stack.push(('end', ()))
                stack = stack.push(('result', ()))
                return stack
            else:
                assert False, "Bad state"
        return Locals.simple(locals), run

Other = compile_function(OtherBuilder())

@dataclass
class BreakBuilder(MachineBuilder):
    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        def run(stack: Stack) -> Stack:
            stack, state = stack.pop()
            assert state == ('start', ()), "Bad state"
            stack = stack.push(('end', ()))
            stack = stack.push(('break', ()))
            return stack
        return {'break': locals, 'return': Locals.make_unreachable(), 'result': Locals.make_unreachable()}, run

Break = BreakBuilder()

@dataclass
class LoopBuilder(MachineBuilder):
    @override
    def __call__(self, locals: Locals) -> tuple[dict[str, Locals], Machine]:
        def run(stack: Stack) -> Stack:
            stack, state = stack.pop()
            assert state == ('start', ()), "Bad state"
            stack = stack.push(('end', ()))
            stack = stack.push(('loop', ()))
            return stack
        return {'loop': locals, 'return': Locals.make_unreachable(), 'result': Locals.make_unreachable()}, run

Loop = LoopBuilder()

@compile_function
@transformer
def string_char_at(value : Value) -> Value:
    s:str
    offset: int
    s, offset = value  # pyright: ignore[reportAssignmentType, reportGeneralTypeIssues]
    return s[offset]  # pyright: ignore[reportArgumentType]

@compile_function
@transformer
def equals(value : Value) -> Value:
    a, b = value  # pyright: ignore[reportGeneralTypeIssues]
    return a == b

@compile_function
@transformer
def str_len(value : Value) -> Value:
    s:str
    s = value  # pyright: ignore[reportAssignmentType, reportGeneralTypeIssues]
    return len(s)


@compile_function
@transformer
def bool_and(value : Value) -> Value:
    a, b = value  # pyright: ignore[reportAssignmentType, reportGeneralTypeIssues]
    return a and b

@compile_function
@transformer
def bool_or(value : Value) -> Value:
    a, b = value  # pyright: ignore[reportAssignmentType, reportGeneralTypeIssues]
    return a or b


@compile_function
@transformer
def bool_not(value : Value) -> Value:
    a = value  # pyright: ignore[reportAssignmentType, reportGeneralTypeIssues]
    return not a

@compile_function
@transformer
def add(value : Value) -> Value:
    a, b = value  # pyright: ignore[reportAssignmentType, reportGeneralTypeIssues]
    return a + b # pyright: ignore[reportOperatorIssue]

string_iter_equals_body = seqn([
    Bind(tuple_binding((
        name_binding('str'),
        name_binding('offset'),
        name_binding('iter'),
    ))),
    Push('next'),
    Move('iter'),
    MakeTuple(2),
    Call(Other),
    Bind(tuple_binding((
        name_binding('iter'),
        name_binding('iter_has_next'),
    ))),
    Copy('str'),
    Call(str_len),
    Copy('offset'),
    MakeTuple(2),
    Call(equals),
    Bind(name_binding('str_done')),
    Copy('str_done'),
    Copy('iter_has_next'),
    Call(bool_not),
    MakeTuple(2),
    Call(bool_and),
    IfThenElse(
        # Both are done.
        seqn([
            Drop('str_done'),
            Drop('iter_has_next'),
            Drop('str'),
            Drop('offset'),
            Drop('iter'),
            Push(True),
            Break,
        ]),
        seqn([
            Move('str_done'),
            Move('iter_has_next'),
            Call(bool_not),
            MakeTuple(2),
            Call(bool_or),
            IfThenElse(
                # Only one is done.
                seqn([
                    Drop('str'),
                    Drop('offset'),
                    Drop('iter'),
                    Push(False),
                    Break,
                ]),
                # Both are not done.
                seqn([
                    Push('iter_clone'),
                    Move('iter'),
                    MakeTuple(2),
                    Call(Other),
                    Bind(tuple_binding((
                        name_binding('iter'),
                        name_binding('char'),
                    ))),
                    Copy('str'),
                    Copy('offset'),
                    MakeTuple(2),
                    Call(string_char_at),
                    Move('char'),
                    MakeTuple(2),
                    Call(equals),
                    IfThenElse(
                        # Chars equal.
                        seqn([
                            Move('str'),
                            Move('offset'),
                            Push(1),
                            MakeTuple(2),
                            Call(add),
                            Move('iter'),
                            MakeTuple(3),
                            Loop,
                        ]),
                        # Chars not equal.
                        seqn([
                            Drop('str'),
                            Drop('offset'),
                            Drop('iter'),
                            Push(False),
                            Break,
                        ]),
                    )
                ]),
            )
        ])
    )
])

# string_iter_equals = seq(do(lambda str, iter: (str, 0, iter)), for_loop(string_iter_equals_body))

# @dot
# def string_iter_next(str, offset):
#     if len(str) == offset:
#         return ('end', ()), ('result', False)
#     else:
#         return (str, offset + 1), ('result', True)

# @dot
# def string_iter_clone(str, offset):
#     return (str, offset), ('result', str[offset])   

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


# string_iter_equals_inverse_handler = seq(
#     do(lambda tag, args: (tag == 'next', (tag, args))),
#     if_then_else(
        
#         do(lambda str, iter: (str, 0, iter)),
#         for_loop(string_iter_equals_body)
#     )
# )


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

def assertTranscript(test : unittest.TestCase, machine : Machine, transcript : list[tuple[Value, Value]]):
    stack = Stack(())
    state = ('start', ())
    while transcript:
        (input, expected_output) = transcript.pop(0)
        stack = stack.push(input)
        stack = stack.push(state)
        stack = machine(stack)
        stack, (action_tag, action_args) = stack.pop()
        stack, state = stack.pop()
        stack, actual_output = stack.pop()
        test.assertEqual((action_tag, actual_output), expected_output)

class TestSimple(unittest.TestCase):
    def test_simple(self):
        transcript : list[tuple[Value, Value]] = [
            ((), ('result', (1, 1, 2))),
        ]
        assertTranscript(self, autopass(simple_test), transcript)

    def test_other(self):
        fn = compile_function(seqn([
            Bind(tuple_binding(())),
            Push(42),
            Bind(name_binding('x')),
            Push(55),
            Bind(name_binding('y')),
            Push('next'),
            Push('iter'),
            MakeTuple(2),
            Call(Other),
            Bind(name_binding('res')),
            Move('x'),
            Move('y'),
            Move('res'),
            MakeTuple(3),
        ]))
        transcript : list[tuple[Value, Value]] = [
            ((), ('other', ('next', 'iter'))),
            ('flarble', ('result', (42, 55, 'flarble'))),
        ]
        assertTranscript(self, autopass(fn), transcript)

class TestStringIterEquals(unittest.TestCase):
    def test_loop_body(self):
        transcript : list[tuple[Value, Value]] = [
            (('foo', 0, 'iter'), ('other', ('next', 'iter'))),
            (('iter', True), ('other', ('iter_clone', 'iter'))),
            (('iter', 'f'), ('loop', ('foo', 1, 'iter'))),
        ]

        locals, machine = string_iter_equals_body(Locals().push_unnamed())
        assertTranscript(self, autopass(machine), transcript)

    def test_loop_body_break(self):
        transcript  : list[tuple[Value, Value]]  = [
            (('foo', 0, 'iter'), ('other', ('next', 'iter'))),
            (('iter', True), ('other', ('iter_clone', 'iter'))),
            (('iter', 'b'), ('break', False)),
        ]
       
        locals, machine = string_iter_equals_body(Locals().push_unnamed())
        assertTranscript(self, autopass(machine), transcript)


#     def test_success(self):
#         transcript = [
#             (('foo', 'iter'), ('other', ('next', 'iter'))),
#             (('iter', True), ('other', ('iter_clone', 'iter'))),
#             (('iter', 'f'), ('other', ('next', 'iter'))),
#             (('iter', True), ('other', ('iter_clone', 'iter'))),
#             (('iter', 'o'), ('other', ('next', 'iter'))),
#             (('iter', True), ('other', ('iter_clone', 'iter'))),
#             (('iter', 'o'), ('other', ('next', 'iter'))),
#             (('iter', False), ('result', True))
#         ]
#         assertTranscript(self, autopass(string_iter_equals), transcript)
        
#     def test_iter_shorter_than_string(self):
#         transcript = [
#             (('foo', 'iter'), ('other', ('next', 'iter'))),
#             (('iter', True), ('other', ('iter_clone', 'iter'))),
#             (('iter', 'f'), ('other', ('next', 'iter'))),
#             (('iter', True), ('other', ('iter_clone', 'iter'))),
#             (('iter', 'o'), ('other', ('next', 'iter'))),
#             (('iter', False), ('result', False))
#         ]
#         assertTranscript(self, autopass(string_iter_equals), transcript)

#     def test_string_shorter_than_iter(self):
#         transcript = [
#             (('f', 'iter'), ('other', ('next', 'iter'))),
#             (('iter', True), ('other', ('iter_clone', 'iter'))),
#             (('iter', 'f'), ('other', ('next', 'iter'))),
#             (('iter', True), ('result', False))
#         ]
#         assertTranscript(self, autopass(string_iter_equals), transcript)

#     def test_char_mismatch(self):
#         transcript = [
#             (('foo', 'iter'), ('other', ('next', 'iter'))),
#             (('iter', True), ('other', ('iter_clone', 'iter'))),
#             (('iter', 'f'), ('other', ('next', 'iter'))),
#             (('iter', True), ('other', ('iter_clone', 'iter'))),
#             (('iter', 'r'), ('result', False))
#         ]
#         assertTranscript(self, autopass(string_iter_equals), transcript)


# def run_tests():
#     """Run all tests and return the test suite."""
#     # Create test suite
#     loader = unittest.TestLoader()
#     suite = unittest.TestSuite()
    
#     # Add test cases to suite
#     suite.addTests(loader.loadTestsFromTestCase(TestSimple))
#     # suite.addTests(loader.loadTestsFromTestCase(TestStringIterEquals))
    
#     return suite



# if __name__ == '__main__':
#     # Run tests with verbose output
#     runner = unittest.TextTestRunner(verbosity=2)
#     suite = run_tests()
#     result = runner.run(suite)
    
#     # Exit with appropriate code
#     sys.exit(not result.wasSuccessful())

if __name__ == '__main__':
    unittest.main()


