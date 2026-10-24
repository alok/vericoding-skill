-- <vc-preamble>
@[reducible, simp]
def firstPositive_precond (a : Array Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def firstPositive (a : Array Int) (h_precond : firstPositive_precond a) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def firstPositive_postcond (a : Array Int) (result : Nat) (h_precond : firstPositive_precond a) : Prop :=
  result < a.size ∧ a[result]! > 0 ∧ ∀ k, k < result → ¬ (a[k]! > 0)

theorem firstPositive_spec_satisfied (a : Array Int) (h_precond : firstPositive_precond a) :
    firstPositive_postcond a (firstPositive a h_precond) h_precond := by
  sorry
-- </vc-theorems>
