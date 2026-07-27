# Hanoi CSP State Machines

Hanoi supports modeling **Communicating Sequential Processes (CSP)** style state machines. Integration tests for these machines are located in the [tests](../tests) directory.

A **CSP Machine** in Hanoi is represented as a module containing standard sentences or functions to manage state initialization (`init`), event acceptance (`accept`), event emission (`emit`), state transitions (`process`), internal/silent transitions (`tau_reduce`), termination status (`is_done`), and checking readiness to finish (`is_ready_to_finish`).

---

## Machine Structure

Every machine module can implement seven standard sentences or functions: `init`, `accept`, `emit`, `process`, `tau_reduce`, `is_done`, and `is_ready_to_finish`. All of these hooks are functions (or sentences) with a strict `1 -> 1` stack arity, operating on structured tuple inputs and outputs.

```
                            [params] (Input to init)
                              │
                              ▼
                           ┌──┴──┐
                           │init │
                           └──┬──┘
                              │
                              ▼  [state]
        ┌─────────────────────┼─────────────────────┐
        │                     │                     │
        ▼                     ▼                     ▼
     [event]               [state]               [event]
        │                     │                     │
        ▼                     ▼                     ▼
   (state, event)          ┌──┴──┐           (event, state)
        │                  │emit │                  │
        ▼                  └──┬──┘                  ▼
    ┌───┴──┐                  │                  ┌───┴───┐
    │accept│                  ▼                  │process│
    └───┬──┘          (has_event, event)         └───┬───┘
        │                                            │
        ▼                                            ▼
      [Bool]                                    [next_state]
```

### 1. `init`
Initializes and pushes the starting state of the machine onto the stack.
* **Stack Input:** A tuple of configuration parameters or arguments (which defaults to `()` if no configuration parameters are required).
* **Stack Output:** The initial state representation (typically a `Tuple`).

### 2. `accept`
Calculates whether the machine is willing to accept a specific passive input event in its current state.
* **Stack Input:** A tuple `(state, event)` where index 0 is the current machine `state` and index 1 is the `event` to evaluate.
* **Stack Output:** A `Bool` (`true` if the event is accepted, `false` otherwise).

### 3. `emit`
Calculates and returns a single event that the machine proactively emits.
* **Stack Input:** The current machine `state`.
* **Stack Output:** A tuple `(has_event, event)` where index 0 is `has_event` (`Bool`) indicating whether an event is emitted, and index 1 is the `event` itself (or `()` if `has_event` is `false`).

### 4. `process`
Computes the next state of the machine after executing a chosen event.
* **Stack Input:** A tuple `(state, event)` where index 0 is the current machine `state` and index 1 is the executed `event`.
* **Stack Output:** Pushes the updated `next_state`.

### 5. `is_done`
Determines if the machine has terminated.
* **Stack Input:** The current machine `state`.
* **Stack Output:** A `Bool` (`true` if the machine has terminated, `false` otherwise).

### 6. `is_ready_to_finish`
Determines if the machine is in a state where it is ready to finish (note that machines that are done must also always be ready to finish).
* **Stack Input:** The current machine `state`.
* **Stack Output:** A `Bool` (`true` if the machine is ready to finish, `false` otherwise).

### 7. `tau_reduce`
Computes an internal/silent transition (tau step) on the state without interacting with the environment.
* **Stack Input:** The current machine `state`.
* **Stack Output:** A tuple `(did_reduce, new_state)` where index 0 is `did_reduce` (`Bool`) indicating if an internal transition was performed, and index 1 is the updated `new_state` (or the original `state` if `did_reduce` is `false`).

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

Here is a simplified version of the character iterator machine from the Hanoi Assembly file [string.hana](../tests/string.hana):

```hana
symbol next "Next character event"
symbol done "Iteration finished event"

mod char_iterator {
    // init: takes the parameter () and returns the initial state (sym, 0)
    function init {
        untuple 0
        push 0
        roll 1
        tuple 2
    }
    
    // accept: takes (state, event) and returns a Bool indicating if the event is accepted.
    // It accepts (next, ch) if idx < len, and (done, ()) if idx == len.
    function accept {
        untuple 2
        // Stack: [event, state]
        untuple 2
        // Stack: [event, idx, sym]
        
        pick 0 // sym
        symbol_len // len (stack: [event, idx, sym, len])
        
        pick 2 // idx
        pick 1 // len
        less
        branch {
            // idx < len: accepts (next, ch) where ch is char at idx
            pick 1 // sym
            pick 3 // idx
            symbol_char_at // ch (stack: [event, idx, sym, len, ch])
            
            push super::next
            tuple 2 // (next, ch) (stack: [event, idx, sym, len, (next, ch)])
            
            roll 4 // Stack: [idx, sym, len, (next, ch), event]
            equal // check if event == (next, ch)
            
            // Clean up: stack has [idx, sym, len, result]
            roll 3 // [sym, len, result, idx]
            drop 0
            roll 2 // [len, result, sym]
            drop 0
            roll 1 // [result, len]
            drop 0 // [result]
        } {
            // idx >= len: check if idx == len
            pick 2 // idx
            pick 1 // len
            equal
            branch {
                // idx == len: accepts (done, ())
                push ()
                push super::done
                tuple 2 // (done, ())
                
                roll 4 // [idx, sym, len, (done, ()), event]
                equal
                
                roll 3; drop 0
                roll 2; drop 0
                roll 1; drop 0
            } {
                // idx > len: accepts nothing (return false)
                drop 3 // drop len, sym, idx
                drop 0 // drop event
                push false
            }
        }
    }
    
    // process: takes (state, event) and transitions (sym, idx) -> (sym, idx + 1)
    function process {
        untuple 2
        // Stack: [event, state]
        drop 1 // Discard event
        untuple 2 // Stack: [idx, sym]
        roll 1 // Stack: [sym, idx]
        push 1
        add
        roll 1 // Stack: [idx + 1, sym]
        tuple 2
    }

    // is_done: takes state (sym, idx) and returns true if idx >= len
    function is_done {
        untuple 2 // Stack: [idx, sym]
        pick 0 // sym
        symbol_len // len (stack: [idx, sym, len])
        
        roll 2 // Stack: [sym, len, idx]
        pick 1 // len
        equal
        branch {
            drop 2
            push true
        } {
            // Check idx > len
            pick 0 // idx
            pick 2 // len
            greater
            branch {
                drop 2
                push true
            } {
                drop 2
                push false
            }
        }
    }
}
```
