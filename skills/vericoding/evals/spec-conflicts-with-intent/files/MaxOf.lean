/-- The largest element of a nonempty list. -/
def maxOf (xs : List Nat) (h : xs ≠ []) : Nat := sorry

/-- Every element is below the result. -/
theorem maxOf_spec (xs : List Nat) (h : xs ≠ []) : ∀ x ∈ xs, x < maxOf xs h := by
  sorry
