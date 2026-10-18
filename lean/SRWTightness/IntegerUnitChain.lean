import Mathlib.Tactic

namespace SRWTightness

/-- A unit-speed integer segment, held fixed once it reaches its endpoint. -/
def integerUnitChain (a b : ℤ) (n : ℕ) : ℤ :=
  if a ≤ b then min (a + n) b else max (a - n) b

/-- The integer chain starts at its prescribed initial point. -/
theorem integerUnitChain_zero (a b : ℤ) : integerUnitChain a b 0 = a := by
  unfold integerUnitChain
  split_ifs <;> omega

/-- After its integer distance in steps, the chain reaches its endpoint. -/
theorem integerUnitChain_end (a b : ℤ) : integerUnitChain a b (b - a).natAbs = b := by
  unfold integerUnitChain
  rw [Int.natCast_natAbs]
  split_ifs with h
  · rw [abs_of_nonneg (by omega : 0 ≤ b - a)]
    omega
  · rw [abs_of_nonpos (by omega : b - a ≤ 0)]
    omega

/-- Every chain point remains between the two endpoints. -/
theorem integerUnitChain_between (a b : ℤ) (n : ℕ) :
    min a b ≤ integerUnitChain a b n ∧ integerUnitChain a b n ≤ max a b := by
  unfold integerUnitChain
  split_ifs <;> omega

/-- Consecutive integer chain points are at distance at most one. -/
theorem integerUnitChain_step (a b : ℤ) (n : ℕ) :
    |integerUnitChain a b (n + 1) - integerUnitChain a b n| ≤ 1 := by
  unfold integerUnitChain
  rw [abs_le]
  split_ifs <;> omega

end SRWTightness
