-- <vc-preamble>
@[reducible, simp]
def findFirst_precond (xs : List Int) (target : Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findFirst (xs : List Int) (target : Int) (h_precond : findFirst_precond xs target) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findFirst_postcond (xs : List Int) (target : Int) (result : Option Nat)
    (h_precond : findFirst_precond xs target) : Prop :=
  match result with
  | some i => ∃ hi : i < xs.length, xs[i] = target ∧ ∀ j (hj : j < i), xs[j]'(by omega) ≠ target
  | none => target ∉ xs

theorem findFirst_spec_satisfied (xs : List Int) (target : Int) (h_precond : findFirst_precond xs target) :
    findFirst_postcond xs target (findFirst xs target h_precond) h_precond := by
  sorry
-- </vc-theorems>
