# The coffee shop, in CCS

An experiment in modelling a concurrent system the way one would in vanilla
Lean 4, knowing nothing of Hanoi: as a labelled transition system built with
the operators of Milner's CCS, with the properties that matter proved as
theorems. The system is the coffee shop of
[`hana/barista.hana`](../hana/barista.hana): two customers, a queue of
orders, and a barista.

## Layout

| File | What it holds |
| --- | --- |
| `CCS/Basic.lean` | Labelled transition systems, reachability and paths; CCS actions (a name, its co-name, silence); parallel composition `∥` and restriction. |
| `CCS/Bisimulation.lean` | Silent and weak steps; strong and weak bisimulation. |
| `CoffeeShop/Basic.lean` | The actors as inductive transition relations, and the shop as their CCS composition. Alice's morning, as a five-step path. |
| `CoffeeShop/Semantics.lean` | `Move`: the shop's steps, read off the composition once with the states written out. Every proof goes through it. |
| `CoffeeShop/Safety.lean` | The invariant of the reachable states, and `right_drink`: whenever a customer drinks, it is their usual. |
| `CoffeeShop/Progress.lean` | `progress`, a measure every silent step lowers, and `everyone_served`: a customer who has asked for coffee can be handed their usual by the shop's own steps. |
| `CoffeeShop/Spec.lean` | The specification `want(c). enjoy(c, c.usual)‾. Spec(c)` for each customer, and `shop_bisimilar_spec`: the shop is weakly bisimilar to it. |

## Building

Install [elan](https://github.com/leanprover/elan). `lean-toolchain` pins
the Lean version and `lake` fetches it on first use.

```bash
cd lean
lake build   # checks everything; there is nothing to run
```

There are no dependencies. Everything is core Lean 4.

## The model

In CCS, with names carrying values and `ā` for the output on `a`:

    Customer(c) = want(c). order(c, c.usual)‾. Σ_d coffee(c, d). enjoy(c, d)‾. Customer(c)
    Queue(xs)   = Σ_o order(o). Queue(xs ++ [o])  +  [xs = o :: rest] next(o)‾. Queue(rest)
    Barista     = Σ_{c,d} next(c, d). coffee(c, d)‾. Barista
    Shop        = (Customer(alice) ∥ Customer(bob) ∥ Queue([]) ∥ Barista) \ {order, next, coffee}

Each actor is a labelled transition system: an inductive type of states and
an inductive transition relation whose constructors are the summands above.
`∥` is CCS parallel composition, in which either side moves alone or the two
handshake on complementary actions and the handshake is silent; `\` is
restriction, which keeps the environment out of the named actions. What the
environment sees is `want(c)` going in and `enjoy(c, d)` coming out.

A customer takes whatever coffee is handed to them, so that everyone getting
the right drink is a property of the shop and not of the customer's
stubbornness. The barista, symmetrically, makes what was ordered and hands it
to whoever ordered it.

## What is proved

- **Everyone gets the right drink.** `right_drink`: from any reachable state,
  a step `enjoy(c, d)` has `d = c.usual`. `right_drink_path` says the same of
  any run from the opening of the shop.
- **Everyone gets served.** `everyone_served`: from any reachable state, a
  customer who is not idle can be brought, by silent steps alone, to holding
  their usual. `progress` is the local form: while anyone is thirsty or
  waiting, the shop has a silent step to take.
- **The shop is its specification.** `shop_bisimilar_spec`: the shop is weakly
  bisimilar to `Spec(alice) ∥ Spec(bob)`, where `Spec(c) = want(c).
  enjoy(c, c.usual)‾. Spec(c)`. This implies the two theorems above, and more:
  no observation the environment can make tells the two apart.

The three theorems depend on no axioms beyond `propext`, `Quot.sound` and
`Classical.choice`; nothing is left as `sorry`.

## How the proofs go

- **One inversion.** `tr_move` reads the shop's steps off the four nested
  compositions once, into the nine constructors of `Move`, and `Move.tr` goes
  back. Every other proof does `cases tr_move ht` and sees nine concrete
  cases with their states written out.
- **The invariant.** `Inv` says three things: the orders in the shop's hands
  (queued, then in the making) contain a customer's order exactly as often as
  `pending` of their phase says, which is once while they wait; every order in
  hand is its customer's usual; and a customer holding coffee holds their
  usual. `inv_step` checks the nine moves; `right_drink` reads the third
  clause off an `enjoy` move.
- **The measure.** `work₁` gives a customer 3 before they order, 2 while their
  order is queued, 1 while it is being made, and `work_lt` shows every silent
  step lowers the sum. `served_of_inv` is then an induction on the work left:
  while a customer is thirsty or waiting, `progress` finds a silent step, and
  the induction hypothesis finishes from the lower state.
- **The bisimulation.** `Spec.R` relates a shop state satisfying `Inv` to the
  pair of what its customers look like from outside, `idle` or `waiting`.
  Forward, a shop step is matched by the same visible step or by nothing;
  backward, the specification's `enjoy` is matched by `served_of_inv` followed
  by the customer's own `enjoy`.

## Where to go next

- **A library instead of `CCS/`.** [CSLib](https://github.com/leanprover/cslib)
  has the same `LTS` shape with a full theory of bisimulation, and a
  formalisation of CCS itself. `CCS/` is 150 lines and exists so the
  experiment has no dependencies.
- **More customers.** The proofs case on `alice` and `bob` by name.
  Parametrising over a finite type of customers means one `Move` per actor
  kind and one case per actor kind in each proof.
- **Fairness.** `everyone_served` says a customer *can* be served by silent
  steps. Saying they *will* be, under any fair scheduling of the shop, needs a
  notion of execution and of fairness on top of `LTS`.
- **The queue's other channel.** The Hanoi queue also answers a non-blocking
  `popFront`. Nothing in the shop uses it, so it is left out here.
