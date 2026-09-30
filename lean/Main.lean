import Hanoi

open Hanoi Hanoi.CoffeeShop

/-- A morning at the open shop: both customers want coffee, and the shop is
left to itself. Prints every event fired and the state reached. -/
def main : IO Unit := do
  let m := shop
  let (opening, s) := m.run 20 m.init
  let some s := m.inject s (.wantCoffee .c1) | throw (IO.userError "customer 1 refused")
  let some s := m.inject s (.wantCoffee .c2) | throw (IO.userError "customer 2 refused")
  let (morning, s) := m.run 20 s
  for e in opening ++ morning do
    IO.println (repr e)
  IO.println s!"settled in: {repr s}"
