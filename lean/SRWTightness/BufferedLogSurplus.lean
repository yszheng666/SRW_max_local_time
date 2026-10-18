import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SRWTightness

/-- A buffer of width at least eight absorbs the universal annulus numerator error. -/
theorem buffered_log_surplus (a H c : ℝ) (ha : 0 < a) (hH : 8 ≤ H) (hHa : H ≤ a)
    (hc : Real.exp 1 * (a + H) ≤ c) :
    1 + 4 / a ≤ Real.log (c / a) := by
  have hsum : 0 < a + H := by linarith
  have hc0 : 0 < c := (mul_pos (Real.exp_pos 1) hsum).trans_le hc
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hsum ha)
  have he : 1 - ((a + H) / a)⁻¹ = H / (a + H) := by
    field_simp
    ring
  rw [he] at hl
  have hf : 4 / a ≤ H / (a + H) := by
    apply (div_le_div_iff₀ ha hsum).mpr
    nlinarith
  have hm := Real.log_le_log (div_pos (mul_pos (Real.exp_pos 1) hsum) ha)
    (div_le_div_of_nonneg_right hc ha.le)
  have hid : Real.log (Real.exp 1 * (a + H) / a) =
      1 + Real.log ((a + H) / a) := by
    rw [mul_div_assoc, Real.log_mul (Real.exp_pos 1).ne' (div_pos hsum ha).ne', Real.log_exp]
  rw [hid] at hm
  linarith

end SRWTightness
