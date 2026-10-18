import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- The quadratic smoothing profile used for convex-event approximation. -/
noncomputable def quadraticCutoff (x : ℝ) : ℝ :=
  if x ≤ 0 then 1 else if x ≤ 1 / 2 then 1 - 2 * x ^ 2
    else if x ≤ 1 then 2 * (1 - x) ^ 2 else 0

/-- Its candidate derivative is a compactly supported triangular function. -/
noncomputable def quadraticCutoffSlope (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if x ≤ 1 / 2 then -4 * x
    else if x ≤ 1 then -4 * (1 - x) else 0

theorem quadraticCutoff_eq_one (x : ℝ) (hx : x ≤ 0) : quadraticCutoff x = 1 := by
  simp [quadraticCutoff, hx]

theorem quadraticCutoff_eq_zero (x : ℝ) (hx : 1 ≤ x) : quadraticCutoff x = 0 := by
  unfold quadraticCutoff
  split_ifs <;> nlinarith

/-- The smoothing profile always takes values in the unit interval. -/
theorem quadraticCutoff_bounds (x : ℝ) : 0 ≤ quadraticCutoff x ∧ quadraticCutoff x ≤ 1 := by
  unfold quadraticCutoff
  split_ifs <;> constructor <;> nlinarith [sq_nonneg x, sq_nonneg (1 - x)]

/-- The profile and its reflection form a partition of unity. -/
theorem quadraticCutoff_reflection (x : ℝ) : quadraticCutoff (1 - x) = 1 - quadraticCutoff x := by
  unfold quadraticCutoff
  split_ifs <;> nlinarith

/-- The candidate derivative has magnitude at most two. -/
theorem quadraticCutoffSlope_bounds (x : ℝ) : -2 ≤ quadraticCutoffSlope x ∧ quadraticCutoffSlope x ≤ 0 := by
  unfold quadraticCutoffSlope
  split_ifs <;> constructor <;> linarith

/-- The candidate derivative has the exact Lipschitz constant needed for smoothing. -/
theorem quadraticCutoffSlope_dist (x y : ℝ) :
    |quadraticCutoffSlope x - quadraticCutoffSlope y| ≤ 4 * |x - y| := by
  unfold quadraticCutoffSlope
  split_ifs <;> apply abs_le.mpr <;> constructor <;>
    linarith [le_abs_self (x - y), neg_abs_le (x - y), abs_nonneg (x - y)]

end SRWTightness
