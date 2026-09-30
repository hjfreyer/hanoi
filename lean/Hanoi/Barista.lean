import Hanoi.Queue

/-!
# The coffee shop

`hana/barista.hana`: two customers, a queue of orders, and a barista, run as
one CSP network. A customer who wants coffee pushes an order onto the queue;
the barista asks the queue for the next order, brews it, and hands the coffee
to its customer, who enjoys it and is idle again.

Where Hanoi tags tuples with symbols and dispatches on the tag, Lean has an
inductive type per alphabet and per state space, and pattern matching. Where
Hanoi closes a machine over its parameters with `compose_static_closure`, a
Lean machine with parameters is a function.
-/

namespace Hanoi.CoffeeShop

inductive CustomerId
  | c1 | c2
  deriving Repr, DecidableEq

inductive Drink
  | latte | espresso
  deriving Repr, DecidableEq

structure Order where
  customer : CustomerId
  drink : Drink
  deriving Repr, DecidableEq

/-- The shop's alphabet. The queue's channels sit under one constructor, which
is what Hanoi's path notation does with a prefix. -/
inductive Event
  /-- A customer decides they want coffee. From the environment. -/
  | wantCoffee (c : CustomerId)
  /-- A customer drinks the coffee they hold. From the environment. -/
  | enjoy (c : CustomerId)
  /-- The barista hands a finished order to its customer. -/
  | coffee (o : Order)
  /-- Traffic on the order queue. -/
  | queue (e : Queue.Event Order)
  deriving Repr, DecidableEq

/-- Read a queue event back out of the shop's alphabet. -/
def Event.queue? : Event → Option (Queue.Event Order)
  | .queue e => some e
  | _ => none

/-! ## Customers -/

namespace Customer

inductive Phase
  | idle | thirsty | ordered | hasCoffee
  deriving Repr, DecidableEq

end Customer

/-- A customer with a fixed id and drink of choice. Hanoi keeps both in the
state, because that is the only place it can keep them; here they are
parameters, and the state is the phase alone. -/
def customer (id : CustomerId) (drink : Drink) : Machine Event Customer.Phase where
  init := .idle
  accept
    | .idle, .wantCoffee c => c == id
    | .ordered, .coffee o => o == ⟨id, drink⟩
    | .hasCoffee, .enjoy c => c == id
    | _, _ => false
  emit
    | .thirsty => some (.queue (.pushBack ⟨id, drink⟩))
    | _ => none
  step
    | .idle, .wantCoffee c => if c == id then some .thirsty else none
    | .thirsty, .queue (.pushBack o) => if o == ⟨id, drink⟩ then some .ordered else none
    | .ordered, .coffee o => if o == ⟨id, drink⟩ then some .hasCoffee else none
    | .hasCoffee, .enjoy c => if c == id then some .idle else none
    | _, _ => none
  tau _ := none
  isDone _ := false
  isReadyToFinish s := s == .idle

/-! ## The barista -/

namespace Barista

inductive State
  /-- About to ask the queue for the next order. -/
  | idle
  /-- Waiting for the queue to answer. -/
  | awaitingOrder
  /-- Making `order`. -/
  | brewing (order : Order)
  deriving Repr, DecidableEq

end Barista

def barista : Machine Event Barista.State where
  init := .idle
  accept
    | .awaitingOrder, .queue (.awaitFront (.resp (some _))) => true
    | _, _ => false
  emit
    | .idle => some (.queue (.awaitFront .req))
    | .awaitingOrder => none
    | .brewing o => some (.coffee o)
  step
    | .idle, .queue (.awaitFront .req) => some .awaitingOrder
    | .awaitingOrder, .queue (.awaitFront (.resp (some o))) => some (.brewing o)
    | .brewing o, .coffee o' => if o == o' then some .idle else none
    | _, _ => none
  tau _ := none
  isDone _ := false
  isReadyToFinish s := s == .idle

/-! ## The network -/

/-- The order queue, speaking the shop's alphabet. -/
def orderQueue : Machine Event (Queue.State Order) :=
  (queue Order).relabel .queue Event.queue?

abbrev Customers.State := Customer.Phase × Customer.Phase
abbrev Shop.State := (Customers.State × Queue.State Order) × Barista.State

/-- The two customers, interleaved: they share no events. -/
def customers : Machine Event Customers.State :=
  (customer .c1 .latte).concurrent (customer .c2 .espresso) fun _ => false

/-- Customers and queue, synchronised on orders being pushed. -/
def customersAndQueue : Machine Event (Customers.State × Queue.State Order) :=
  customers.concurrent orderQueue fun
    | .queue (.pushBack _) => true
    | _ => false

/-- The whole shop, synchronised on the barista's traffic: its requests to the
queue, and the coffee it hands over. Everything is still visible. -/
def shop : Machine Event Shop.State :=
  customersAndQueue.concurrent barista fun
    | .queue (.awaitFront _) | .coffee _ => true
    | _ => false

/-- The shop with its internal traffic hidden. Only `wantCoffee` and `enjoy`
(and the unused `popFront` channel) remain for the environment. -/
def hiddenShop : Machine Event Shop.State :=
  shop.hide fun
    | .queue (.pushBack _) | .queue (.awaitFront _) | .coffee _ => true
    | _ => false

end Hanoi.CoffeeShop
