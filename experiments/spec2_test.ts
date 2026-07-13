import { primitive, valueSet, tupleSet, anySet } from "./value";
import {
  stop,
  skip,
  prefix,
  externalChoice,
  internalChoice,
  parallel,
  sequence,
  hiding,
  lazy,
  getTransitions,
} from "./spec2";

describe("CSP Engine (spec2.ts)", () => {
  const e1 = primitive("a");
  const e2 = primitive("b");
  const e3 = primitive("c");

  it("STOP has no transitions", () => {
    expect(getTransitions(stop())).toEqual([]);
  });

  it("SKIP has a tick transition", () => {
    const transitions = getTransitions(skip());
    expect(transitions.length).toBe(1);
    expect(transitions[0].kind).toBe("tick");
    expect(transitions[0].next).toEqual(stop());
  });

  it("Prefix offers a visible transition", () => {
    const p = prefix(e1, stop());
    const transitions = getTransitions(p);
    expect(transitions.length).toBe(1);
    expect(transitions[0]).toEqual({
      kind: "visible",
      event: e1,
      next: stop(),
    });
  });

  it("Lazy processes resolve recursively", () => {
    // Define an infinite stream of 'a's: A = a -> A
    const aStream = lazy(() => prefix(e1, aStream));
    const transitions = getTransitions(aStream);
    expect(transitions.length).toBe(1);
    expect(transitions[0].kind).toBe("visible");
    expect((transitions[0] as any).event).toEqual(e1);
    // Checking the next step also yields 'a'
    const nextTransitions = getTransitions((transitions[0] as any).next);
    expect(nextTransitions.length).toBe(1);
    expect((nextTransitions[0] as any).event).toEqual(e1);
  });

  it("Internal choice offers tau transitions to choices", () => {
    const p = internalChoice(prefix(e1, stop()), prefix(e2, stop()));
    const transitions = getTransitions(p);
    expect(transitions).toEqual([
      { kind: "internal", next: prefix(e1, stop()) },
      { kind: "internal", next: prefix(e2, stop()) },
    ]);
  });

  it("External choice choice preservation and resolution", () => {
    // P = (a -> STOP) [] (b -> STOP)
    const p = externalChoice(prefix(e1, stop()), prefix(e2, stop()));
    const transitions = getTransitions(p);
    // Both visible events are immediately offered, resolving the choice
    expect(transitions).toEqual([
      { kind: "visible", event: e1, next: stop() },
      { kind: "visible", event: e2, next: stop() },
    ]);

    // Q = (a -> STOP) [] (b -> STOP) [] (tau -> c -> STOP)
    // Q should offer 'a', 'b', and a 'tau' leading to choice preservation of 'a' and 'b' but with the third option resolved
    const q = externalChoice(
      prefix(e1, stop()),
      internalChoice(prefix(e2, stop()), prefix(e3, stop())),
    );
    const qTrans = getTransitions(q);
    expect(qTrans.some((t) => t.kind === "visible" && t.event === e1)).toBe(true);
    expect(qTrans.some((t) => t.kind === "internal")).toBe(true);
  });

  it("Sequence executes first then second", () => {
    // P = SKIP ; (a -> STOP)
    const p = sequence(skip(), prefix(e1, stop()));
    const transitions = getTransitions(p);
    // Since SKIP has a tick, it immediately transitions to the second process via a tau (internal) transition
    expect(transitions.length).toBe(1);
    expect(transitions[0].kind).toBe("internal");
    expect(transitions[0].next).toEqual(prefix(e1, stop()));

    // Q = (a -> SKIP) ; (b -> STOP)
    const q = sequence(prefix(e1, skip()), prefix(e2, stop()));
    const qTrans = getTransitions(q);
    expect(qTrans).toEqual([
      {
        kind: "visible",
        event: e1,
        next: sequence(skip(), prefix(e2, stop())),
      },
    ]);
  });

  it("Hiding converts matching events to internal transitions", () => {
    // P = (a -> STOP) \ {a}
    const p = hiding(prefix(e1, stop()), valueSet(e1));
    const transitions = getTransitions(p);
    expect(transitions.length).toBe(1);
    expect(transitions[0].kind).toBe("internal");
    expect(transitions[0].next).toEqual(hiding(stop(), valueSet(e1)));

    // Q = (b -> STOP) \ {a}
    const q = hiding(prefix(e2, stop()), valueSet(e1));
    const qTrans = getTransitions(q);
    expect(qTrans[0].kind).toBe("visible");
    expect((qTrans[0] as any).event).toEqual(e2);
  });

  it("Parallel composition executes independent and synchronized events", () => {
    // Left: a -> b -> STOP
    // Right: a -> c -> STOP
    // Synchronized on {a}
    const left = prefix(e1, prefix(e2, stop()));
    const right = prefix(e1, prefix(e3, stop()));
    const syncSet = valueSet(e1);

    const p = parallel(left, syncSet, right);
    const transitions = getTransitions(p);

    // Both must synchronize on 'a'
    expect(transitions.length).toBe(1);
    expect(transitions[0].kind).toBe("visible");
    expect((transitions[0] as any).event).toEqual(e1);

    // After 'a', the state is: (b -> STOP) [| {a} |] (c -> STOP)
    // Since 'b' and 'c' are not in the syncSet, they can occur in any order (interleaving)
    const nextState = (transitions[0] as any).next;
    const nextTrans = getTransitions(nextState);
    expect(nextTrans.length).toBe(2);
    expect(nextTrans.some((t) => t.kind === "visible" && t.event === e2)).toBe(true);
    expect(nextTrans.some((t) => t.kind === "visible" && t.event === e3)).toBe(true);
  });
});
