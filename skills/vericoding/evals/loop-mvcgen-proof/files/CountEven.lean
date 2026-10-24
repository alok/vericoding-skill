import Std.Tactic.Do
open Std.Do

/-- How many elements of `xs` are even. -/
def countEven (xs : List Nat) : Nat := Id.run do
  let mut c := 0
  for x in xs do
    if x % 2 = 0 then c := c + 1
  return c

theorem countEven_spec (xs : List Nat) : countEven xs = (xs.filter (· % 2 = 0)).length := by
  sorry
