# Hanoi CSP State Machines

This directory contains Hanoi integration tests, including modeling of **Communicating Sequential Processes (CSP)** style state machines.

A **CSP Machine** in Hanoi is represented as a module containing standard sentences (functions) to manage state initialization (`init`), event acceptance (`accept`), event emission (`emit`), state transitions (`process`), internal/silent transitions (`tau_reduce`), termination status (`is_done`), and checking readiness to finish (`is_ready_to_finish`).

---

## Machine Structure

Every machine module can implement seven standard sentences: `init`, `accept`, `emit`, `process`, `tau_reduce`, `is_done`, and `is_ready_to_finish`.

```
                  [sym / params]  (Input to init)
                        │
                        ▼
                     ┌──┴──┐
                     │init │
                     └──┬──┘
                        │
                        ▼  [state]
         ┌──────────────┼──────────────┐
         ▼              ▼              ▼
     ┌───┴──┐       ┌───┴──┐       ┌───┴───┐
     │accept│       │ emit │       │process│ ◄─── [event]
     └───┬──┘       └───┬──┘       └───┬───┘
         │              │              │
         ▼              ▼              ▼
    [ValueSet]     [ValueSet]     [next_state]
(Accepted events)(Emitted events)
```

### 1. `init`
Initializes and pushes the starting state of the machine onto the stack.
* **Stack Input:** Optionally pops configuration arguments or parameters.
* **Stack Output:** Pushes the initial state representation (typically a `Tuple`).

### 2. `accept`
Calculates and returns a set of events that the machine is currently willing to accept (passive/input events).
* **Stack Input:** Pops the current `state`.
* **Stack Output:** Pushes a `ValueSet` containing the accepted events. If the machine has terminated or accepts no inputs in its current state, it pushes `empty_set`.

### 3. `emit`
Calculates and returns a single event that the machine proactively emits (output event).
* **Stack Input:** Pops the current `state`.
* **Stack Output:** Pushes a tuple `(event, has_event)`. If the machine emits an event, `has_event` is `true`. If the machine emits no events in its current state, `has_event` is `false` (in which case the first element of the tuple is ignored, e.g., `()`).


### 4. `process`
Computes the next state of the machine after executing a chosen event.
* **Stack Input:** Pops `event` (top of stack) and then `state` (second-to-top).
* **Stack Output:** Pushes the new updated `state`.

### 5. `is_done`
Determines if the machine has terminated.
* **Stack Input:** Pops the current `state`.
* **Stack Output:** Pushes a `Boolean` (`true` if the machine is done, `false` otherwise).

### 6. `is_ready_to_finish`
Determines if the machine is in a state where it is ready to finish (note that machines that are done must also always be ready to finish).
* **Stack Input:** Pops the current `state`.
* **Stack Output:** Pushes a `Boolean` (`true` if the machine is ready to finish, `false` otherwise).

### 7. `tau_reduce`
Computes an internal/silent transition (tau step) on the state without interacting with the environment.
* **Stack Input:** Pops the current `state`.
* **Stack Output:** Pushes a tuple `(new_state, changed)` where `changed` is a `Boolean` indicating if an internal transition was performed. If no internal transition occurred, it returns `(state, false)`.

---

## Design Patterns & Conventions

Under the `(tag, args)` convention, the tag or state symbol is placed at the first index of the tuple (index 0). Symmetrically, calling `untuple(N)` on a tuple pushes elements onto the stack in reverse order of the tuple's elements, placing index 0 (the tag or state symbol) at the top of the stack.

### State Representation
Machine state is typically represented as a `Tuple` starting with the current state symbol:
* **Customer State:** `(internal_state_symbol, (preferred_drink, id))`
* **Character Iterator State:** `(symbol, current_index)`

### Event Representation
Events are usually represented as a `Tuple` starting with the event identifier symbol:
* **Coffee Order Event:** `(order, (drink_symbol, customer_id))`
* **Iterator Step Event:** `(next, character_unicode_codepoint)`
* **Iterator Finished Event:** `(done, ())`

### Path Notation
Events can also be structured using **Path Notation** (dot notation) to represent hierarchical namespaces.
* **Path Notation:** `foo.bar.baz` corresponds to `(foo, (bar, (baz, ())))` (where `foo` is the outermost tag and `baz` is the innermost event).

---

## Example: A Simple Iterator Machine

Here is a simplified version of the character iterator machine from `string.hana`:

```hana
symbol next "Next character event"
symbol done "Iteration finished event"

mod char_iterator {
    // init: takes a symbol, returns (sym, 0)
    function init {
        push 0
        roll 1
        tuple 2
    }
    
    // accept: returns {(next, ch)} if idx < len, {(done, ())} if idx == len, or empty_set
    function accept {
        pick 0
        untuple 2
        
        pick 0 // sym
        symbol_len // len
        
        pick 2 // idx
        pick 1 // len
        less
        branch {
            // idx < len: Get character and return {(next, ch)}
            pick 1 // sym
            pick 3 // idx
            symbol_char_at
            
            push super::next
            tuple 2
            set_singleton
            
            // Clean up
            drop 4; drop 3; drop 2; drop 1
        } {
            // idx >= len: Check if idx == len
            pick 2 // idx
            pick 1 // len
            equal
            branch {
                // idx == len: Return {(done, ())}
                push ()
                push super::done
                tuple 2
                set_singleton
                drop 4; drop 3; drop 2; drop 1
            } {
                // idx > len: Return empty_set
                push empty_set
                drop 4; drop 3; drop 2; drop 1
            }
        }
    }
    
    // process: transitions (sym, idx) -> (sym, idx + 1)
    function process {
        drop 0 // Discard event
        untuple 2 // Stack: [idx, sym]
        roll 1 // Stack: [sym, idx]
        push 1
        add
        roll 1 // Stack: [idx + 1, sym]
        tuple 2
    }
}
```
