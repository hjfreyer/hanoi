import { Value, ValueSet, contains, equals } from "./value";

export type ProcessSpec =
  | { kind: "stop" }
  | { kind: "skip" }
  | { kind: "prefix"; event: Value; next: ProcessSpec }
  | { kind: "externalChoice"; choices: ProcessSpec[] }
  | { kind: "internalChoice"; choices: ProcessSpec[] }
  | { kind: "parallel"; left: ProcessSpec; alphabet: ValueSet; right: ProcessSpec }
  | { kind: "sequence"; first: ProcessSpec; second: ProcessSpec }
  | { kind: "hiding"; inner: ProcessSpec; hidden: ValueSet }
  | { kind: "lazy"; resolve: () => ProcessSpec };

export type Transition =
  | { kind: "visible"; event: Value; next: ProcessSpec }
  | { kind: "internal"; next: ProcessSpec }
  | { kind: "tick"; next: ProcessSpec };

/**
 * STOP process (deadlock). Offers no transitions.
 */
export function stop(): ProcessSpec {
  return { kind: "stop" };
}

/**
 * SKIP process (successful termination). Can perform a tick transition to STOP.
 */
export function skip(): ProcessSpec {
  return { kind: "skip" };
}

/**
 * Prefix operator (event -> next). Performs the event, then behaves like next.
 */
export function prefix(event: Value, next: ProcessSpec): ProcessSpec {
  return { kind: "prefix", event, next };
}

/**
 * External choice operator (P [] Q). The environment determines which choice is taken
 * based on the first visible event. Internal transitions preserve the choice.
 */
export function externalChoice(...choices: ProcessSpec[]): ProcessSpec {
  return { kind: "externalChoice", choices };
}

/**
 * Internal choice operator (P |~| Q). The process non-deterministically chooses
 * one of the options via an internal transition.
 */
export function internalChoice(...choices: ProcessSpec[]): ProcessSpec {
  return { kind: "internalChoice", choices };
}

/**
 * Parallel composition operator (P [| alphabet |] Q). Both processes run concurrently,
 * synchronizing on events in the alphabet set. Other visible events can occur independently.
 * Both processes must synchronize on successful termination (tick).
 */
export function parallel(
  left: ProcessSpec,
  alphabet: ValueSet,
  right: ProcessSpec,
): ProcessSpec {
  return { kind: "parallel", left, alphabet, right };
}

/**
 * Sequential composition operator (P ; Q). Behaves like P until P terminates successfully (tick),
 * then behaves like Q.
 */
export function sequence(first: ProcessSpec, second: ProcessSpec): ProcessSpec {
  return { kind: "sequence", first, second };
}

/**
 * Hiding operator (P \ hidden). Events in the hidden set are made internal (converted to tau/internal transitions).
 */
export function hiding(inner: ProcessSpec, hidden: ValueSet): ProcessSpec {
  return { kind: "hiding", inner, hidden };
}

/**
 * Lazy recursive process definition. Helps define infinite or mutually recursive processes.
 */
export function lazy(resolve: () => ProcessSpec): ProcessSpec {
  return { kind: "lazy", resolve };
}

/**
 * Computes all possible one-step transitions for a given ProcessSpec.
 */
export function getTransitions(proc: ProcessSpec): Transition[] {
  switch (proc.kind) {
    case "stop":
      return [];

    case "skip":
      return [{ kind: "tick", next: stop() }];

    case "prefix":
      return [{ kind: "visible", event: proc.event, next: proc.next }];

    case "lazy":
      return getTransitions(proc.resolve());

    case "internalChoice":
      return proc.choices.map((choice) => ({
        kind: "internal",
        next: choice,
      }));

    case "externalChoice": {
      const transitions: Transition[] = [];
      for (let i = 0; i < proc.choices.length; i++) {
        const choice = proc.choices[i];
        const innerTrans = getTransitions(choice);
        for (const t of innerTrans) {
          if (t.kind === "internal") {
            // Internal transitions preserve choice
            const nextChoices = [...proc.choices];
            nextChoices[i] = t.next;
            transitions.push({
              kind: "internal",
              next: externalChoice(...nextChoices),
            });
          } else {
            // Visible transitions (and ticks) resolve choice
            transitions.push(t);
          }
        }
      }
      return transitions;
    }

    case "sequence": {
      const transitions: Transition[] = [];
      const innerTrans = getTransitions(proc.first);
      for (const t of innerTrans) {
        if (t.kind === "internal") {
          transitions.push({
            kind: "internal",
            next: sequence(t.next, proc.second),
          });
        } else if (t.kind === "tick") {
          // When first completes, transition to second
          transitions.push({
            kind: "internal",
            next: proc.second,
          });
        } else {
          transitions.push({
            kind: "visible",
            event: t.event,
            next: sequence(t.next, proc.second),
          });
        }
      }
      return transitions;
    }

    case "hiding": {
      const transitions: Transition[] = [];
      const innerTrans = getTransitions(proc.inner);
      for (const t of innerTrans) {
        if (t.kind === "internal") {
          transitions.push({
            kind: "internal",
            next: hiding(t.next, proc.hidden),
          });
        } else if (t.kind === "tick") {
          transitions.push({
            kind: "tick",
            next: hiding(t.next, proc.hidden),
          });
        } else {
          if (contains(proc.hidden, t.event)) {
            // Event matches hidden set -> becomes internal transition
            transitions.push({
              kind: "internal",
              next: hiding(t.next, proc.hidden),
            });
          } else {
            // Not hidden -> stays visible
            transitions.push({
              kind: "visible",
              event: t.event,
              next: hiding(t.next, proc.hidden),
            });
          }
        }
      }
      return transitions;
    }

    case "parallel": {
      const transitions: Transition[] = [];
      const leftTrans = getTransitions(proc.left);
      const rightTrans = getTransitions(proc.right);

      // 1. Left moves independently (for tau and visible events not in alphabet)
      for (const lt of leftTrans) {
        if (lt.kind === "internal") {
          transitions.push({
            kind: "internal",
            next: parallel(lt.next, proc.alphabet, proc.right),
          });
        } else if (lt.kind === "visible" && !contains(proc.alphabet, lt.event)) {
          transitions.push({
            kind: "visible",
            event: lt.event,
            next: parallel(lt.next, proc.alphabet, proc.right),
          });
        }
      }

      // 2. Right moves independently (for tau and visible events not in alphabet)
      for (const rt of rightTrans) {
        if (rt.kind === "internal") {
          transitions.push({
            kind: "internal",
            next: parallel(proc.left, proc.alphabet, rt.next),
          });
        } else if (rt.kind === "visible" && !contains(proc.alphabet, rt.event)) {
          transitions.push({
            kind: "visible",
            event: rt.event,
            next: parallel(proc.left, proc.alphabet, rt.next),
          });
        }
      }

      // 3. Synchronized moves (events in alphabet)
      for (const lt of leftTrans) {
        if (lt.kind === "visible" && contains(proc.alphabet, lt.event)) {
          for (const rt of rightTrans) {
            if (
              rt.kind === "visible" &&
              contains(proc.alphabet, rt.event) &&
              equals(lt.event, rt.event)
            ) {
              transitions.push({
                kind: "visible",
                event: lt.event,
                next: parallel(lt.next, proc.alphabet, rt.next),
              });
            }
          }
        }
      }

      // 4. Synchronized ticks (both must terminate)
      for (const lt of leftTrans) {
        if (lt.kind === "tick") {
          for (const rt of rightTrans) {
            if (rt.kind === "tick") {
              transitions.push({
                kind: "tick",
                next: parallel(lt.next, proc.alphabet, rt.next),
              });
            }
          }
        }
      }

      return transitions;
    }
  }
}
