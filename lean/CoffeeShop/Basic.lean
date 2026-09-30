import CCS.Basic

/-!
# A coffee shop, in CCS

Two customers, a queue of orders, and a barista. In CCS one would write, with
names carrying values and `ā` for the output on `a`:

    Customer(c) = want(c). order(c, c.usual)‾. Σ_d coffee(c, d). enjoy(c, d)‾. Customer(c)
    Queue(xs)   = Σ_o order(o). Queue(xs ++ [o])  +  [xs = o :: rest] next(o)‾. Queue(rest)
    Barista     = Σ_{c,d} next(c, d). coffee(c, d)‾. Barista
    Shop        = (Customer(alice) ∥ Customer(bob) ∥ Queue([]) ∥ Barista) \ {order, next, coffee}

A customer takes whatever coffee is handed to them and drinks it, so that the
shop handing everyone the right drink is something to prove, not something
the customer enforces.

Each process is given below as a labelled transition system: a state space,
and an inductive transition relation whose constructors are the summands
above. The shop is the CCS composition of the four.
-/

namespace CoffeeShop

open CCS

inductive Customer
  | alice | bob
  deriving DecidableEq, Repr

inductive Drink
  | latte | espresso
  deriving DecidableEq, Repr

structure Order where
  customer : Customer
  drink : Drink
  deriving DecidableEq, Repr

/-- Everyone has their usual. -/
def Customer.usual : Customer → Drink
  | .alice => .latte
  | .bob => .espresso

/-- The order a customer places. -/
def Customer.order (c : Customer) : Order := ⟨c, c.usual⟩

@[simp] theorem Customer.usual_alice : Customer.alice.usual = .latte := rfl
@[simp] theorem Customer.usual_bob : Customer.bob.usual = .espresso := rfl
@[simp] theorem Customer.order_alice : Customer.alice.order = ⟨.alice, .latte⟩ := rfl
@[simp] theorem Customer.order_bob : Customer.bob.order = ⟨.bob, .espresso⟩ := rfl

/-- The names the shop communicates on, each carrying its value. -/
inductive Msg
  /-- The environment tells a customer they want coffee. -/
  | want (c : Customer)
  /-- A customer places an order with the queue. -/
  | order (o : Order)
  /-- The queue hands the barista the next order. -/
  | next (o : Order)
  /-- The barista hands customer `c` a `d`. -/
  | coffee (c : Customer) (d : Drink)
  /-- Customer `c` drinks a `d`, for the environment to see. -/
  | enjoy (c : Customer) (d : Drink)
  deriving DecidableEq, Repr

/-- The names the shop keeps to itself. -/
def Msg.internal : Msg → Bool
  | .order _ | .next _ | .coffee _ _ => true
  | .want _ | .enjoy _ _ => false

/-! ## The actors -/

namespace Customer

inductive Phase
  | idle | thirsty | waiting
  /-- Holding a `d`. -/
  | served (d : Drink)
  deriving DecidableEq, Repr

/-- `Customer(c) = want(c). order(c, c.usual)‾. Σ_d coffee(c, d). enjoy(c, d)‾. Customer(c)` -/
inductive Step (c : Customer) : Phase → Act Msg → Phase → Prop
  | want : Step c .idle (.inp (.want c)) .thirsty
  | order : Step c .thirsty (.out (.order c.order)) .waiting
  | coffee (d : Drink) : Step c .waiting (.inp (.coffee c d)) (.served d)
  | enjoy (d : Drink) : Step c (.served d) (.out (.enjoy c d)) .idle

abbrev lts (c : Customer) : LTS Phase (Act Msg) := ⟨Step c⟩

end Customer

namespace Queue

/-- `Queue(xs) = Σ_o order(o). Queue(xs ++ [o]) + [xs = o :: rest] next(o)‾. Queue(rest)` -/
inductive Step : List Order → Act Msg → List Order → Prop
  | push (xs : List Order) (o : Order) : Step xs (.inp (.order o)) (xs ++ [o])
  | pop (o : Order) (xs : List Order) : Step (o :: xs) (.out (.next o)) xs

abbrev lts : LTS (List Order) (Act Msg) := ⟨Step⟩

end Queue

namespace Barista

inductive State
  | idle
  | brewing (o : Order)
  deriving DecidableEq, Repr

/-- `Barista = Σ_{c,d} next(c, d). coffee(c, d)‾. Barista`: make what was
ordered, and hand it to whoever ordered it. -/
inductive Step : State → Act Msg → State → Prop
  | take (o : Order) : Step .idle (.inp (.next o)) (.brewing o)
  | serve (c : Customer) (d : Drink) : Step (.brewing ⟨c, d⟩) (.out (.coffee c d)) .idle

abbrev lts : LTS State (Act Msg) := ⟨Step⟩

end Barista

/-! ## The shop -/

namespace Shop

abbrev State := ((Customer.Phase × Customer.Phase) × List Order) × Barista.State

/-- Nobody wants anything yet. -/
def init : State := (((.idle, .idle), []), .idle)

/-- Where a customer is. -/
def State.phase (s : State) : Customer → Customer.Phase
  | .alice => s.1.1.1
  | .bob => s.1.1.2

/-- What the queue holds. -/
@[simp] def State.queue (s : State) : List Order := s.1.2

/-- What the barista is doing. -/
@[simp] def State.barista (s : State) : Barista.State := s.2

@[simp] theorem State.phase_alice (pa pb : Customer.Phase) (xs : List Order) (b : Barista.State) :
    State.phase (((pa, pb), xs), b) .alice = pa := rfl
@[simp] theorem State.phase_bob (pa pb : Customer.Phase) (xs : List Order) (b : Barista.State) :
    State.phase (((pa, pb), xs), b) .bob = pb := rfl

end Shop

/-- `Shop = (Customer(alice) ∥ Customer(bob) ∥ Queue([]) ∥ Barista) \ {order, next, coffee}` -/
abbrev shop : LTS Shop.State (Act Msg) :=
  (Customer.lts .alice ∥ Customer.lts .bob ∥ Queue.lts ∥ Barista.lts).restrict Msg.internal

/-- Alice's morning, step by step: she wants coffee, orders, the queue passes
the order on, the barista hands it over, she drinks. Three of the five steps
are handshakes the environment does not see. -/
example : shop.Path Shop.init
    [.inp (.want .alice), .tau, .tau, .tau, .out (.enjoy .alice .latte)] Shop.init :=
  .cons (.mk (.left (.left (.left .want))) rfl) <|
  .cons (.mk (.left (.comm (.left .order) (.push [] _) nofun)) trivial) <|
  .cons (.mk (.comm (.right (.pop _ [])) (.take _) nofun) trivial) <|
  .cons (.mk (.comm (.left (.left (.coffee _))) (.serve _ _) nofun) trivial) <|
  .cons (.mk (.left (.left (.left (.enjoy _)))) rfl) .nil

end CoffeeShop
