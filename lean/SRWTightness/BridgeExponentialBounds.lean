import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

namespace SRWTightness

/-- Quantitative reflection-factor bounds, with explicit constants on [0,1]. -/
theorem bridge_reflection_factor_bounds (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    z / 2 ≤ 1 - Real.exp (-z) ∧ 1 - Real.exp (-z) ≤ z := by
  have hu := Real.add_one_le_exp (-z)
  have he : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
  have hp : 0 ≤ Real.exp (-z) := (Real.exp_pos _).le
  have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp z) hp
  have hid : Real.exp z * Real.exp (-z) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hid] at hm
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr he)]
  · linarith

end SRWTightness
