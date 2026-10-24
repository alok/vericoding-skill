-- <vc-preamble>
@[reducible, simp]
def findFirst_precond (xs : List Int) (target : Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findFirst (xs : List Int) (target : Int) (h_precond : findFirst_precond xs target) : Option Nat :=
  match xs with
  | [] => none
  | x :: rest =>
    if x = target then some 0
    else (findFirst rest target trivial).map (· + 1)

-- Lemmas about the implementation go after it, inside the same replacement:
-- `vc-helpers` comes before `vc-definitions`, so it can't mention `findFirst`.
theorem findFirst_correct (xs : List Int) (target : Int) (h : findFirst_precond xs target) :
    match findFirst xs target h with
    | some i => ∃ hi : i < xs.length, xs[i] = target ∧ ∀ j (hj : j < i), xs[j]'(by omega) ≠ target
    | none => target ∉ xs := by
  induction xs with
  | nil => simp [findFirst]
  | cons x rest ih =>
    by_cases hx : x = target
    · simp [findFirst, hx]
    · have ih := ih trivial
      cases hr : findFirst rest target trivial with
      | none =>
        simp only [hr] at ih
        simp only [findFirst, hx, ↓reduceIte, hr, Option.map_none, List.mem_cons, not_or]
        exact ⟨Ne.symm hx, ih⟩
      | some k =>
        simp only [hr] at ih
        obtain ⟨hk, hkt, hlt⟩ := ih
        simp only [findFirst, hx, ↓reduceIte, hr, Option.map_some]
        refine ⟨by simp; omega, by simpa using hkt, ?_⟩
        intro j hj
        cases j with
        | zero => simpa using hx
        | succ j => simpa using hlt j (by omega)
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
  have := findFirst_correct xs target h_precond
  simp only [findFirst_postcond]
  split <;> simp_all
-- </vc-theorems>
