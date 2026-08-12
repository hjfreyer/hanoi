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
   (event, state)          ┌──┴──┐           (event, state)
        │                  │emit │                  │
        ▼                  └──┬──┘                  ▼
    ┌───┴──┐                  │                  ┌───┴───┐
    │accept│                  ▼                  │process│
    └───┬──┘          (event, has_event)         └───┬───┘
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
* **Stack Input:** A tuple `(event, state)` where index 1 is the current machine `state` — on top, where `untuple 2` leaves it — and index 0 is the `event` to evaluate.
* **Stack Output:** A `Bool` (`true` if the event is accepted, `false` otherwise).

### 3. `emit`
Calculates and returns a single event that the machine proactively emits.
* **Stack Input:** The current machine `state`.
* **Stack Output:** A tuple `(event, has_event)` where index 1 is `has_event` (`Bool`) indicating whether an event is emitted, and index 0 is the `event` itself (or `()` if `has_event` is `false`).

### 4. `process`
Computes the next state of the machine after executing a chosen event.
* **Stack Input:** A tuple `(event, state)` where index 1 is the current machine `state` and index 0 is the executed `event`.
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
* **Stack Output:** A tuple `(new_state, did_reduce)` where index 1 is `did_reduce` (`Bool`) indicating if an internal transition was performed, and index 0 is the updated `new_state` (or the original `state` if `did_reduce` is `false`).

---

## Design Patterns & Conventions

Under the `(args, tag)` convention, the tag or state symbol is placed at the *last* index of the tuple, which is the one `tuple N` took off the top of the stack. Symmetrically, `untuple N` pushes the elements back in index order, so the tag or state symbol lands on top again, where the code that dispatches on it wants it.

### State Representation
Machine state is typically represented as a `Tuple` ending with the current state symbol:
* **Customer State:** `((id, preferred_drink), internal_state_symbol)`
* **Character Iterator State:** `(current_index, const_string)`

### Event Representation
Events are usually represented as a `Tuple` ending with the event identifier symbol:
* **Coffee Order Event:** `((customer_id, drink_symbol), order)`
* **Iterator Step Event:** `(character_unicode_codepoint, next)`
* **Iterator Finished Event:** `((), done)`

### Path Notation
Events can also be structured using **Path Notation** (dot notation) to represent hierarchical namespaces.
* **Path Notation:** `foo.bar.baz` corresponds to `((((), baz), bar), foo)` (where `foo` is the outermost tag and `baz` is the innermost event).

---

## Example: A Simple Iterator Machine

Here is a simplified version of the character iterator machine from the Hanoi Assembly file [string.hana](../tests/string.hana):

```hana
symbol next
symbol done

mod char_iterator {
    // init: takes the parameter () and returns the initial state (0, sym)
    function init {
        untuple 0
        push 0
        roll 1
        tuple 2
    }
    
    // accept: takes (event, state) and returns a Bool indicating if the event is accepted.
    // It accepts (ch, next) if idx < len, and ((), done) if idx == len.
    function accept {
        untuple 2
        // Stack: [event, state]
        untuple 2
        // Stack: [event, idx, sym]
        
        pick 0 // sym
        const_string_len // len (stack: [event, idx, sym, len])
        
        pick 2 // idx
        pick 1 // len
        less
        branch {
            // idx < len: accepts (ch, next) where ch is char at idx
            pick 1 // sym
            pick 3 // idx
            const_string_char_at // ch (stack: [event, idx, sym, len, ch])
            
            push super::next
            tuple 2 // (ch, next) (stack: [event, idx, sym, len, (ch, next)])
            
            roll 4 // Stack: [idx, sym, len, (ch, next), event]
            equal // check if event == (ch, next)
            
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
                // idx == len: accepts ((), done)
                push ()
                push super::done
                tuple 2 // ((), done)
                
                roll 4 // [idx, sym, len, ((), done), event]
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
    
    // process: takes (event, state) and transitions (idx, sym) -> (idx + 1, sym)
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

    // is_done: takes state (idx, sym) and returns true if idx >= len
    function is_done {
        untuple 2 // Stack: [idx, sym]
        pick 0 // sym
        const_string_len // len (stack: [idx, sym, len])
        
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
