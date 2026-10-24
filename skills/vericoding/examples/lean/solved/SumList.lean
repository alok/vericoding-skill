import Std.Tactic.Do
open Std.Do

/-- Imperative-style sum. The loop is the implementation; the spec is `List.sum`. -/
def sumList (xs : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in xs do
    acc := acc + x
  return acc

theorem sumList_spec (xs : List Nat) : sumList xs = xs.sum := by
  generalize h : sumList xs = r
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨cur, acc⟩ => ⌜acc = cur.prefix.sum⌝
  all_goals mleave; grind
