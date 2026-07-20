# Hanoi CSP State Machines

This directory contains Hanoi integration tests, including modeling of **Communicating Sequential Processes (CSP)** style state machines.

A **CSP Machine** in Hanoi is represented as a module containing three standard sentences (functions) to manage state initialization, event acceptance, and state transitions.

---

## Machine Structure

Every machine module must implement three sentences: `init`, `accept`, and `process`.

```
                  [sym / params]  (Input to init)
                        │
                        ▼
                     ┌──┴──┐
                     │init │
                     └──┬──┘
                        │
                        ▼  [state]
                        ├──────────────────────┐
                        ▼                      ▼
                    ┌───┴──┐               ┌───┴───┐
                    │accept│               │process│ ◄─── [event]
                    └───┬──┘               └───┬───┘
                        │                      │
                        ▼                      ▼
                   [ValueSet]            [next_state]
               (Accepted events)
```

### 1. `init`
Initializes and pushes the starting state of the machine onto the stack.
* **Stack Input:** Optionally pops configuration arguments or parameters.
* **Stack Output:** Pushes the initial state representation (typically a `Tuple`).

### 2. `accept`
Calculates and returns a set of events that the machine is currently willing to participate in.
* **Stack Input:** Pops the current `state`.
* **Stack Output:** Pushes a `ValueSet` containing the accepted events. If the machine has terminated or is blocked, it pushes `empty_set`.

### 3. `process`
Computes the next state of the machine after executing a chosen event.
* **Stack Input:** Pops `event` (top of stack) and then `state` (second-to-top).
* **Stack Output:** Pushes the new updated `state`.

---

## Design Patterns & Conventions

### State Representation
Machine state is typically represented as a `Tuple` of variables:
* **Customer State:** `(id, preferred_drink, internal_state_symbol)`
* **Character Iterator State:** `(symbol, current_index)`

### Event Representation
Events are usually represented as a `Tuple` consisting of an event identifier symbol followed by payload values:
* **Coffee Order Event:** `(order, customer_id, drink_symbol)`
* **Iterator Step Event:** `(next, character_unicode_codepoint)`
* **Iterator Finished Event:** `(done, ())`

---

## Example: A Simple Iterator Machine

Here is a simplified version of the character iterator machine from `string.hana`:

```hana
symbol next "Next character event"
symbol done "Iteration finished event"

mod char_iterator {
    # init: takes a symbol, returns (sym, 0)
    init {
        push 0
        tuple 2
    }
    
    # accept: returns {(next, ch)} if idx < len, {(done, ())} if idx == len, or empty_set
    accept {
        pick 0
        untuple 2
        
        pick 1 # sym
        symbol_len # len
        
        pick 1 # idx
        pick 1 # len
        less
        branch {
            # idx < len: Get character and return {(next, ch)}
            pick 2 # sym
            pick 2 # idx
            symbol_char_at
            
            push super::next
            roll 1
            tuple 2
            set_singleton
            
            # Clean up
            drop 4; drop 3; drop 2; drop 1
        } {
            # idx >= len: Check if idx == len
            pick 1 # idx
            pick 1 # len
            equal
            branch {
                # idx == len: Return {(done, ())}
                push super::done
                tuple 0
                tuple 2
                set_singleton
                drop 4; drop 3; drop 2; drop 1
            } {
                # idx > len: Return empty_set
                push empty_set
                drop 4; drop 3; drop 2; drop 1
            }
        }
    }
    
    # process: transitions (sym, idx) -> (sym, idx + 1)
    process {
        drop 0 # Discard event
        untuple 2
        push 1
        add
        tuple 2
    }
}
```
