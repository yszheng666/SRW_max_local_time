import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

namespace SRWTightness

/-- A dyadic half-side can be chosen between four and eight times any radius at least one. -/
theorem exists_buffered_dyadic_half_side (r : ℝ) (hr : 1 ≤ r) :
    ∃ k : ℕ, 4 * r ≤ (2 : ℝ) ^ (k + 1) ∧ (2 : ℝ) ^ (k + 1) ≤ 8 * r := by
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ 4 * r by linarith) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨k, hk'.le, ?_⟩
  rw [pow_succ]
  linarith

end SRWTightness
