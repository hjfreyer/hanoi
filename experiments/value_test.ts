import {
  primitive,
  tuple,
  isPrimitive,
  isTuple,
  equals,
  ValueSet,
  anySet,
  noneSet,
  valueSet,
  unionSet,
  tupleSet,
  complementSet,
  contains,
} from "./value";

describe("Value type", () => {
  it("can construct primitive and tuple values", () => {
    const p = primitive(42);
    const t = tuple(primitive("hello"), primitive(true));

    expect(p).toEqual({ kind: "primitive", value: 42 });
    expect(t).toEqual({
      kind: "tuple",
      elements: [
        { kind: "primitive", value: "hello" },
        { kind: "primitive", value: true },
      ],
    });
  });

  it("identifies primitive and tuple values using type guards", () => {
    const p = primitive(42);
    const t = tuple(primitive("hello"));

    expect(isPrimitive(p)).toBe(true);
    expect(isPrimitive(t)).toBe(false);

    expect(isTuple(p)).toBe(false);
    expect(isTuple(t)).toBe(true);
  });

  it("checks equality recursively", () => {
    const v1 = tuple(primitive(1), tuple(primitive(2), primitive(3)));
    const v2 = tuple(primitive(1), tuple(primitive(2), primitive(3)));
    const v3 = tuple(primitive(1), tuple(primitive(2), primitive(4)));

    expect(equals(v1, v2)).toBe(true);
    expect(equals(v1, v3)).toBe(false);
    expect(equals(primitive(42), primitive(42)).valueOf()).toBe(true);
    expect(equals(primitive(42), primitive("42")).valueOf()).toBe(false);
    expect(equals(primitive(42), tuple(primitive(42))).valueOf()).toBe(false);
  });

  describe("ValueSet and membership", () => {
    const val1 = primitive(1);
    const val2 = primitive(2);
    const valTuple = tuple(primitive(1), primitive(2));

    it("anySet matches any value", () => {
      const set = anySet();
      expect(contains(set, val1)).toBe(true);
      expect(contains(set, valTuple)).toBe(true);
    });

    it("noneSet matches no value", () => {
      const set = noneSet();
      expect(contains(set, val1)).toBe(false);
      expect(contains(set, valTuple)).toBe(false);
    });

    it("valueSet matches only specific value", () => {
      const set = valueSet(val1);
      expect(contains(set, val1)).toBe(true);
      expect(contains(set, val2)).toBe(false);
    });

    it("unionSet matches if any inner set matches", () => {
      const set = unionSet(valueSet(val1), valueSet(val2));
      expect(contains(set, val1)).toBe(true);
      expect(contains(set, val2)).toBe(true);
      expect(contains(set, valTuple)).toBe(false);
    });

    it("tupleSet matches tuples element-wise", () => {
      const set = tupleSet(valueSet(val1), anySet());
      expect(contains(set, valTuple)).toBe(true);
      expect(contains(set, tuple(primitive(2), primitive(2)))).toBe(false);
      expect(contains(set, val1)).toBe(false);
    });

    it("complementSet matches values not in the inner set", () => {
      const set = complementSet(valueSet(val1));
      expect(contains(set, val1)).toBe(false);
      expect(contains(set, val2)).toBe(true);
      expect(contains(set, valTuple)).toBe(true);
    });
  });
});
