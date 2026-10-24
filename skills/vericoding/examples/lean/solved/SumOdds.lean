/-- Sum of the first `n` odd numbers: 1 + 3 + ... + (2n - 1). -/
def sumOdds (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => sumOdds k + (2 * k + 1)

/-- The closed form. -/
theorem sumOdds_spec (n : Nat) : sumOdds n = n * n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumOdds, ih]; grind
