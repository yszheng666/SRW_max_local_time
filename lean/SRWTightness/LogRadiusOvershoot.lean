import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace SRWTightness

/-- A unit radial overshoot changes the logarithm by at most two divided by the radius. -/
theorem log_radius_unit_error (r R : ℝ) (hR : 2 ≤ R)
    (hrl : R - 1 ≤ r) (hru : r ≤ R + 1) : |Real.log r - Real.log R| ≤ 2 / R := by
  have hR0 : 0 < R := by linarith
  have hr0 : 0 < r := by linarith
  have hu := Real.log_le_sub_one_of_pos (div_pos hr0 hR0)
  have hl := Real.log_le_sub_one_of_pos (div_pos hR0 hr0)
  rw [Real.log_div hr0.ne' hR0.ne'] at hu
  rw [Real.log_div hR0.ne' hr0.ne'] at hl
  have hupper : r / R - 1 ≤ 2 / R := by
    apply (le_div_iff₀ hR0).mpr
    have he : (r / R - 1) * R = r - R := by field_simp <;> ring
    rw [he]
    linarith
  have hlower : R / r - 1 ≤ 2 / R := by
    apply (le_div_iff₀ hR0).mpr
    apply (mul_le_mul_iff_right₀ hr0).mp
    have he : r * ((R / r - 1) * R) = R * (R - r) := by field_simp <;> ring
    rw [he]
    nlinarith
  exact abs_le.mpr ⟨by linarith [hl.trans hlower], hu.trans hupper⟩

end SRWTightness
