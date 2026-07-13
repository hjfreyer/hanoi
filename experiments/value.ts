export type Value =
  | { kind: "primitive"; value: any }
  | { kind: "tuple"; elements: Value[] };

/**
 * Creates a primitive Value.
 */
export function primitive(value: any): Value {
  return { kind: "primitive", value };
}

/**
 * Creates a tuple Value.
 */
export function tuple(...elements: Value[]): Value {
  return { kind: "tuple", elements };
}

/**
 * Type guard for primitive values.
 */
export function isPrimitive(
  val: Value,
): val is { kind: "primitive"; value: any } {
  return val.kind === "primitive";
}

/**
 * Type guard for tuple values.
 */
export function isTuple(
  val: Value,
): val is { kind: "tuple"; elements: Value[] } {
  return val.kind === "tuple";
}

/**
 * Recursively checks equality of two Value instances.
 */
export function equals(a: Value, b: Value): boolean {
  if (a.kind !== b.kind) return false;
  if (a.kind === "primitive") {
    return a.value === (b as { kind: "primitive"; value: any }).value;
  }
  const aTuple = a;
  const bTuple = b as { kind: "tuple"; elements: Value[] };
  if (aTuple.elements.length !== bTuple.elements.length) return false;
  return aTuple.elements.every((el, i) => equals(el, bTuple.elements[i]));
}

export type ValueSet =
  | { kind: "any" }
  | { kind: "none" }
  | { kind: "value"; value: Value }
  | { kind: "union"; sets: ValueSet[] }
  | { kind: "tuple"; elements: ValueSet[] }
  | { kind: "complement"; inner: ValueSet };

/**
 * Matches any Value.
 */
export function anySet(): ValueSet {
  return { kind: "any" };
}

/**
 * Matches no Value.
 */
export function noneSet(): ValueSet {
  return { kind: "none" };
}

/**
 * Matches a specific Value.
 */
export function valueSet(value: Value): ValueSet {
  return { kind: "value", value };
}

/**
 * Matches any value that matches at least one of the given sets.
 */
export function unionSet(...sets: ValueSet[]): ValueSet {
  return { kind: "union", sets };
}

/**
 * Matches a tuple Value if it has the same number of elements as this set,
 * and each element matches the corresponding set element.
 */
export function tupleSet(...elements: ValueSet[]): ValueSet {
  return { kind: "tuple", elements };
}

/**
 * Matches any Value that does not match the inner set.
 */
export function complementSet(inner: ValueSet): ValueSet {
  return { kind: "complement", inner };
}

/**
 * Checks if a Value is a member of the given ValueSet.
 */
export function contains(set: ValueSet, val: Value): boolean {
  switch (set.kind) {
    case "any":
      return true;
    case "none":
      return false;
    case "value":
      return equals(set.value, val);
    case "union":
      return set.sets.some((s) => contains(s, val));
    case "tuple":
      if (val.kind !== "tuple") return false;
      if (val.elements.length !== set.elements.length) return false;
      return val.elements.every((el, i) => contains(set.elements[i], el));
    case "complement":
      return !contains(set.inner, val);
  }
}

