// Test file for experiments.ts
// import { Machine, t, FuncFragment, func, Function, closure, Action } from './experiments';

import assert from "assert";

type Context = {
  named: { [key: string]: any },
  unnamed: any[],
}

function name_binding(name: string) {
  return (ctx: Context): Context => {

    return {
      named: {
        ...ctx.named,
        [name]: ctx.unnamed[0],
      },
      unnamed: ctx.unnamed.slice(1),
    }
  };
}

function tuple_binding(bindings: ((ctx: Context) => Context)[]) {
  return (ctx: Context): Context => {
    const popped = ctx.unnamed[0];
    assert(popped.length === bindings.length);
    // Remove the tuple from unnamed stack
    ctx = { named: { ...ctx.named }, unnamed: ctx.unnamed.slice(1) };
    for (let i = 0; i < bindings.length; i++) {
      ctx = { named: { ...ctx.named }, unnamed: [popped[i], ...ctx.unnamed] };
      ctx = bindings[i](ctx);
    }
    return ctx;
  }
}

function drop_binding() {
  return (ctx: Context): Context => {
    return { named: { ...ctx.named }, unnamed: ctx.unnamed.slice(1) };
  }
}

function literal_binding(value: any) {
  return (ctx: Context): Context => {
    const popped = ctx.unnamed[0];
    assert(popped === value);
    return { named: { ...ctx.named }, unnamed: ctx.unnamed.slice(1) };
  }
}

function copy(name: string) {
  return (ctx: Context): Context => {
    return { named: { ...ctx.named }, unnamed: [ctx.named[name], ...ctx.unnamed] };
  }
}

function mv(name: string) {
  return (ctx: Context): Context => {
    const popped = ctx.named[name];
    delete ctx.named[name];
    return { named: { ...ctx.named }, unnamed: [popped, ...ctx.unnamed] };
  }
}

function push(value: any) {
  return (ctx: Context): Context => {
    return { named: { ...ctx.named }, unnamed: [value, ...ctx.unnamed] };
  }
}

function tuple(size: number) {
  return (ctx: Context): Context => {
    return { named: { ...ctx.named }, unnamed: [ctx.unnamed.slice(0, size), ...ctx.unnamed.slice(size)] };
  }
}

// x => *x yield x => *x x tuple(2) 'add yield () => 42 return

// seq(
//   bind x {start} (1 unnamed) -> {end} result(1 named, 0 unnamed)
//   copy x {start} (1 named, 0 unnamed) -> {end} result(1 named, 1 unnamed)
//   yield {start} (1 named, 1 unnamed) -> awaiting{all but 1 unnamed} yield(1 unnamed)
//)

// x => loop {
//   x == 42 if {
//     'ok' return
//   } else {
//     'nope' yield x => continue
//   }
// }

// seq (
//   bind x
//   loop (seq(
//     x 42 tuple(2) 'eq if (
//       seq('ok' return)
//     )
//   ))
// )

describe('binding functions', () => {
  describe('name_binding', () => {
    test('binds value from unnamed to named', () => {
      const ctx: Context = {
        named: {},
        unnamed: [42]
      };
      const binding = name_binding('x');
      const result = binding(ctx);

      expect(result.named).toEqual({ x: 42 });
      expect(result.unnamed).toEqual([]);
    });

    test('preserves existing named values', () => {
      const ctx: Context = {
        named: { y: 10 },
        unnamed: [42]
      };
      const binding = name_binding('x');
      const result = binding(ctx);

      expect(result.named).toEqual({ x: 42, y: 10 });
      expect(result.unnamed).toEqual([]);
    });

    test('removes value from unnamed stack', () => {
      const ctx: Context = {
        named: {},
        unnamed: [42, 100, 200]
      };
      const binding = name_binding('x');
      const result = binding(ctx);

      expect(result.named).toEqual({ x: 42 });
      expect(result.unnamed).toEqual([100, 200]);
    });

    test('overwrites existing named value with same name', () => {
      const ctx: Context = {
        named: { x: 10 },
        unnamed: [42]
      };
      const binding = name_binding('x');
      const result = binding(ctx);

      expect(result.named).toEqual({ x: 42 });
      expect(result.unnamed).toEqual([]);
    });
  });

  describe('tuple_binding', () => {
    test('binds tuple elements to multiple bindings', () => {
      const ctx: Context = {
        named: {},
        unnamed: [[1, 2, 3]]
      };
      const binding = tuple_binding([
        name_binding('a'),
        name_binding('b'),
        name_binding('c')
      ]);
      const result = binding(ctx);

      expect(result.named).toEqual({ a: 1, b: 2, c: 3 });
      expect(result.unnamed).toEqual([]);
    });

    test('preserves existing named values', () => {
      const ctx: Context = {
        named: { existing: 'value' },
        unnamed: [[10, 20]]
      };
      const binding = tuple_binding([
        name_binding('x'),
        name_binding('y')
      ]);
      const result = binding(ctx);

      expect(result.named).toEqual({ existing: 'value', x: 10, y: 20 });
      expect(result.unnamed).toEqual([]);
    });

    test('handles empty tuple', () => {
      const ctx: Context = {
        named: {},
        unnamed: [[]]
      };
      const binding = tuple_binding([]);
      const result = binding(ctx);

      expect(result.named).toEqual({});
      expect(result.unnamed).toEqual([]);
    });

    test('handles nested bindings', () => {
      const ctx: Context = {
        named: {},
        unnamed: [[[1, 2], 3]]
      };
      const binding = tuple_binding([
        tuple_binding([name_binding('a'), name_binding('b')]),
        name_binding('c')
      ]);
      const result = binding(ctx);

      expect(result.named).toEqual({ a: 1, b: 2, c: 3 });
      expect(result.unnamed).toEqual([]);
    });

    test('preserves remaining unnamed values', () => {
      const ctx: Context = {
        named: {},
        unnamed: [[1, 2], 99, 100]
      };
      const binding = tuple_binding([
        name_binding('x'),
        name_binding('y')
      ]);
      const result = binding(ctx);

      expect(result.named).toEqual({ x: 1, y: 2 });
      expect(result.unnamed).toEqual([99, 100]);
    });
  });

  describe('drop_binding', () => {
    test('drops value from unnamed stack', () => {
      const ctx: Context = {
        named: {},
        unnamed: [42]
      };
      const binding = drop_binding();
      const result = binding(ctx);

      expect(result.named).toEqual({});
      expect(result.unnamed).toEqual([]);
    });

    test('preserves named values', () => {
      const ctx: Context = {
        named: { x: 10, y: 20 },
        unnamed: [42]
      };
      const binding = drop_binding();
      const result = binding(ctx);

      expect(result.named).toEqual({ x: 10, y: 20 });
      expect(result.unnamed).toEqual([]);
    });

    test('drops only first value from unnamed stack', () => {
      const ctx: Context = {
        named: {},
        unnamed: [42, 100, 200]
      };
      const binding = drop_binding();
      const result = binding(ctx);

      expect(result.named).toEqual({});
      expect(result.unnamed).toEqual([100, 200]);
    });
  });

  describe('literal_binding', () => {
    test('matches and removes literal number', () => {
      const ctx: Context = {
        named: {},
        unnamed: [42]
      };
      const binding = literal_binding(42);
      const result = binding(ctx);

      expect(result.named).toEqual({});
      expect(result.unnamed).toEqual([]);
    });

    test('matches and removes literal string', () => {
      const ctx: Context = {
        named: {},
        unnamed: ['hello']
      };
      const binding = literal_binding('hello');
      const result = binding(ctx);

      expect(result.named).toEqual({});
      expect(result.unnamed).toEqual([]);
    });

    test('matches and removes literal boolean', () => {
      const ctx: Context = {
        named: {},
        unnamed: [true]
      };
      const binding = literal_binding(true);
      const result = binding(ctx);

      expect(result.named).toEqual({});
      expect(result.unnamed).toEqual([]);
    });

    test('preserves named values', () => {
      const ctx: Context = {
        named: { x: 10 },
        unnamed: [42]
      };
      const binding = literal_binding(42);
      const result = binding(ctx);

      expect(result.named).toEqual({ x: 10 });
      expect(result.unnamed).toEqual([]);
    });

    test('preserves remaining unnamed values', () => {
      const ctx: Context = {
        named: {},
        unnamed: [42, 100, 200]
      };
      const binding = literal_binding(42);
      const result = binding(ctx);

      expect(result.named).toEqual({});
      expect(result.unnamed).toEqual([100, 200]);
    });

    test('throws assertion error on mismatch', () => {
      const ctx: Context = {
        named: {},
        unnamed: [42]
      };
      const binding = literal_binding(100);

      expect(() => binding(ctx)).toThrow();
    });
  });
});

type Machine = (state: any, ctx: Context) => [any, any, Context];

function t(f: (ctx: Context) => Context): Machine {
  return (state: any, ctx: Context): [any, any, Context] => {
    assert(state.kind === 'start');
    return [{kind: 'end'}, 'result', f(ctx)];
  }
}

function seq(...machines: Machine[]): Machine {
  return (state: any, ctx: Context): [any, any, Context] => {
    while (true) {
      if (state.kind === 'start') {
        state = {kind: 'inner', idx: 0, inner: {kind: 'start'}};
      }      
      let idx = state.idx;
      let inner = state.inner;
      
      if (idx === machines.length) {
        assert(false, "End of sequence: " + JSON.stringify(state));
      }

      let [new_inner, action, new_ctx] = machines[idx](inner, ctx);
      if (action === 'result') {
        state = {kind: 'inner', idx: idx + 1, inner: {kind: 'start'}};
        ctx = new_ctx;
      } else {
        return [{kind: 'inner', idx, inner: new_inner}, action, new_ctx];
      }
    }
  }
}

describe('t function', () => {
  test('transforms context with name_binding', () => {
    const ctx: Context = {
      named: {},
      unnamed: [42]
    };
    const machine = t(name_binding('x'));
    const [state, action, result] = machine({kind: 'start'}, ctx);

    expect(state).toEqual({kind: 'end'});
    expect(action).toBe('result');
    expect(result.named).toEqual({ x: 42 });
    expect(result.unnamed).toEqual([]);
  });

  test('transforms context with drop_binding', () => {
    const ctx: Context = {
      named: { x: 10 },
      unnamed: [42, 100]
    };
    const machine = t(drop_binding());
    const [state, action, result] = machine({kind: 'start'}, ctx);

    expect(state).toEqual({kind: 'end'});
    expect(action).toBe('result');
    expect(result.named).toEqual({ x: 10 });
    expect(result.unnamed).toEqual([100]);
  });

  test('transforms context with literal_binding', () => {
    const ctx: Context = {
      named: {},
      unnamed: [42]
    };
    const machine = t(literal_binding(42));
    const [state, action, result] = machine({kind: 'start'}, ctx);

    expect(state).toEqual({kind: 'end'});
    expect(action).toBe('result');
    expect(result.named).toEqual({});
    expect(result.unnamed).toEqual([]);
  });

  test('throws on invalid state', () => {
    const ctx: Context = {
      named: {},
      unnamed: [42]
    };
    const machine = t(name_binding('x'));

    expect(() => machine({kind: 'invalid'}, ctx)).toThrow();
  });
});

function yld(): Machine {
  return (state: any, ctx: Context): [any, any, Context] => {
    if (state.kind === 'start') {
      const popped = ctx.unnamed[0];
      return [{kind: 'awaiting', ctx: {named: { ...ctx.named }, unnamed: ctx.unnamed.slice(1)}}, 'yield', {named: {}, unnamed: [popped]}];
    }
    if (state.kind === 'awaiting') {
      assert(Object.keys(ctx.named).length === 0);
      assert(ctx.unnamed.length === 1);
      const popped = ctx.unnamed[0];

      return [{kind: 'end'}, 'result', {named: { ...state.ctx.named }, unnamed: [popped, ...state.ctx.unnamed]}];
    }
    assert(false, "Bad state: " + JSON.stringify(state));
  }
}

describe('combining seq and yld', () => {
  test('pushes then yields', () => {
    let ctx: Context = {
      named: {},
      unnamed: [1]
    };
    const machine = fn(
      t(name_binding('x')),
      t(push(2)),
      yld(),
      t(mv('x')),
      t(tuple(2)),
      ret()
    );
    
    let state;
    let action;
    [state, action, ctx] = machine({kind: 'start'}, ctx);
    
    expect(ctx.named).toEqual({});
    expect(ctx.unnamed).toEqual([2]);
    
    // Continue to yield
    [state, action, ctx] = machine(state, {
      named: {},
      unnamed: [42]
    });
    
    // Should return what we passed in.
    expect(state.kind).toBe('end');
    expect(action).toBe('return');
    expect(ctx.named).toEqual({});
    expect(ctx.unnamed).toEqual([[1, 42]]);
  });
});

function loop_impl(body: Machine): Machine {
  return (state: any, ctx: Context): [any, any, Context] => {
    while (true) {
      if (state.kind === 'start') {
        state = {kind: 'inner', inner: {kind: 'start'}};
      }
      if (state.kind === 'inner') {
        const [new_state, action, new_ctx] = body(state.inner, ctx);

        if (action === 'break') {
          return [{kind: 'end'}, 'result', new_ctx];
        } else if (action === 'continue') {
          state = {kind: 'inner', inner: {kind: 'start'}};
          ctx = new_ctx;
        } else if (action === 'yield') {
          return [{kind: 'inner', inner: new_state}, 'yield', new_ctx];
        } else if (action === 'return') {
          return [{kind: 'end'}, 'return', new_ctx];
        } else {
          assert(false, "Bad action: " + action);
        }
      } else {
        assert(false, "Bad state: " + JSON.stringify(state));
      }
    }
  }
}

function loop(...body: Machine[]): Machine {
  return loop_impl(seq(...body));
}

function fn_impl(body: Machine): Machine {
  return (state: any, ctx: Context): [any, any, Context] => {
    if (state.kind === 'start') {
      state = {kind: 'inner', inner: {kind: 'start'}};
    }
    if (state.kind === 'inner') {
      const [new_state, action, new_ctx] = body(state.inner, ctx);
      if (action === 'return') {
        return [{kind: 'end'}, 'return', new_ctx];
      } else if (action === 'yield') {
        return [{kind: 'inner', inner: new_state}, 'yield', new_ctx];
      } else {
        return [{kind: 'inner', inner: new_state}, action, new_ctx];
      }
    }
    assert(false, "Bad state: " + JSON.stringify(state));
  }
}

function fn(...body: Machine[]): Machine {
  return fn_impl(seq(...body));
}

function ret(): Machine {
  return (state: any, ctx: Context): [any, any, Context] => {
    return [{kind: 'end'}, 'return', ctx];
  }
}

function cont(): Machine {
  return (state: any, ctx: Context): [any, any, Context] => {
    return [{kind: 'end'}, 'continue', ctx];
  }
}

function add(): Machine {
  return (state: any, ctx: Context): [any, any, Context] => {
    const a = ctx.unnamed[0];
    const b = ctx.unnamed[1];
    return [{kind: 'end'}, 'result', {named: { ...ctx.named }, unnamed: [a + b, ...ctx.unnamed.slice(2)]}];
  }
}

describe('loop function', () => {
  test('loops over sequence', () => {
    const doubler = fn(
      t(name_binding('x')),
      loop(
        t(copy('x')),
        t(mv('x')),
        add(),
        yld(),
        t(name_binding('x')),
        cont(),
      ),
    );

    const ctx: Context = {
      named: {},
      unnamed: [4]
    };
    let [state, action, result] = doubler({kind: 'start'}, ctx);

    expect(action).toEqual('yield');
    expect(result.named).toEqual({});
    expect(result.unnamed).toEqual([8]);

    [state, action, result] = doubler(state, {
      named: {},
      unnamed: [8]
    });

    expect(action).toEqual('yield');
    expect(result.named).toEqual({});
    expect(result.unnamed).toEqual([16]);
  });
});