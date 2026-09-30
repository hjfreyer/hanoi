import Hanoi.Barista

/-!
# The coffee shop, exercised

The `test sentence`s of `hana/barista.hana`, as Lean checks. Each `#guard`
evaluates its claim when the file is elaborated, so `lake build` is the test
run; each `example … := by decide` has the kernel do the same evaluation as a
proof.

Two of Hanoi's tests have no counterpart. `verify_customer_is_event` and
`verify_emit_totality` check that values have the shapes the machine expects,
which the types here settle before anything runs.
-/

namespace Hanoi.CoffeeShop

def order1 : Order := ⟨.c1, .latte⟩
def order2 : Order := ⟨.c2, .espresso⟩

/-! ## One customer (`verify_customer_logic`) -/

/-- Customer 1 through one cycle: wants coffee, orders, is served, enjoys. -/
def customerCycle : Option Customer.Phase := do
  let m := customer .c1 .latte
  let s ← m.inject .idle (.wantCoffee .c1)
  guard (s = .thirsty)
  let s ← m.emits s (.queue (.pushBack order1))
  guard (s = .ordered)
  let s ← m.inject s (.coffee order1)
  guard (s = .hasCoffee)
  m.inject s (.enjoy .c1)

#guard customerCycle = some .idle
example : customerCycle = some .idle := by decide

-- A customer's events are their own.
#guard (customer .c1 .latte).accept .idle (.wantCoffee .c2) = false
#guard (customer .c1 .latte).accept .ordered (.coffee order2) = false

/-! ## The barista alone (`verify_barista_rejection`) -/

-- Coffee is what the barista emits, never what it accepts.
#guard barista.accept .idle (.coffee order1) = false
-- Orders reach the barista through the queue, never directly.
#guard barista.accept .idle (.queue (.pushBack order1)) = false
-- An idle barista asks the queue for the next order, ...
#guard barista.emit .idle = some (.queue (.awaitFront .req))
-- ... and, having asked, takes the answer, ...
#guard barista.accept .awaitingOrder (.queue (.awaitFront (.resp (some order1)))) = true
-- ... but offers no coffee before it has one.
#guard barista.emit .awaitingOrder = none

/-! ## The hidden network (`verify_hidden_system`)

Only the customers' decisions come from outside; everything between
customers, queue and barista happens as silent steps. -/

def afterFirstOrder : Shop.State := (((.hasCoffee, .idle), .awaitingPush), .awaitingOrder)
def afterBothOrders : Shop.State := (((.hasCoffee, .hasCoffee), .awaitingPush), .awaitingOrder)
def afterFirstEnjoy : Shop.State := (((.idle, .hasCoffee), .awaitingPush), .awaitingOrder)
def afterBothEnjoy : Shop.State := (((.idle, .idle), .awaitingPush), .awaitingOrder)

/-- The states the hidden shop settles in after each event from outside. -/
def hiddenScenario : Option (List Shop.State) := do
  let m := hiddenShop
  let s ← m.inject m.init (.wantCoffee .c1)
  let s₁ := m.quiesce 20 s
  let s ← m.inject s₁ (.wantCoffee .c2)
  let s₂ := m.quiesce 20 s
  let s₃ ← m.inject s₂ (.enjoy .c1)
  let s₄ ← m.inject s₃ (.enjoy .c2)
  pure [s₁, s₂, s₃, s₄]

#guard hiddenScenario = some [afterFirstOrder, afterBothOrders, afterFirstEnjoy, afterBothEnjoy]
example :
    hiddenScenario = some [afterFirstOrder, afterBothOrders, afterFirstEnjoy, afterBothEnjoy] := by
  decide

-- Nothing internal leaks: the hidden shop has no event of its own to fire.
#guard (hiddenShop.run 20 afterFirstOrder).1 = []

/-! ## The open network (`verify_concurrent_system`)

The same story with nothing hidden, so the test fires each internal event by
hand, in the order Hanoi's test does. -/

def openScenario : Option Shop.State := do
  let m := shop
  let s := m.init
  -- The barista asks the queue for an order; there is none, so the queue waits.
  let s ← m.emits s (.queue (.awaitFront .req))
  -- Both customers decide they want coffee.
  let s ← m.inject s (.wantCoffee .c1)
  let s ← m.inject s (.wantCoffee .c2)
  -- Customer 1 orders, and the waiting queue hands the order straight on.
  let s ← m.emits s (.queue (.pushBack order1))
  let s ← m.emits s (.queue (.awaitFront (.resp (some order1))))
  -- Customer 2 orders; the queue holds it. Hanoi takes two silent steps here
  -- to append; the Lean queue appends at once.
  let s ← m.emits s (.queue (.pushBack order2))
  -- Customer 1 is served, and enjoys.
  let s ← m.emits s (.coffee order1)
  let s ← m.inject s (.enjoy .c1)
  -- The barista asks again and is answered at once.
  let s ← m.emits s (.queue (.awaitFront .req))
  let s ← m.emits s (.queue (.awaitFront (.resp (some order2))))
  -- Customer 2 is served, and enjoys.
  let s ← m.emits s (.coffee order2)
  m.inject s (.enjoy .c2)

#guard openScenario = some (((.idle, .idle), .idle []), .idle)
example : openScenario = some (((.idle, .idle), .idle []), .idle) := by decide

/-- Left to itself once both customers want coffee, the open shop fires its
internal events in this order: the left side of each composition goes first,
so customer 2's order lands on the queue before customer 1's coffee is done. -/
def openTrace : Option (List Event × Shop.State) := do
  let m := shop
  let (es₀, s) := m.run 20 m.init
  let s ← m.inject s (.wantCoffee .c1)
  let s ← m.inject s (.wantCoffee .c2)
  let (es, s) := m.run 20 s
  pure (es₀ ++ es, s)

#guard openTrace = some
  ([ .queue (.awaitFront .req),
     .queue (.pushBack order1),
     .queue (.awaitFront (.resp (some order1))),
     .queue (.pushBack order2),
     .coffee order1,
     .queue (.awaitFront .req),
     .queue (.awaitFront (.resp (some order2))),
     .coffee order2,
     .queue (.awaitFront .req) ],
   afterBothOrders)

end Hanoi.CoffeeShop
