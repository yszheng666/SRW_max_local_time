import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SRWTightness

/-- Beyond one quarter of the terminal radius, the source error scale is bounded below. -/
theorem half_radius_terminal_error (m a : ℝ) (hm : 0 < m) (ha : 0 < a)
    (hlo : m / 4 ≤ a) (hhi : a ≤ m / 2) :
    Real.log 2 / 4 ≤ ((a + 1) / m) * Real.log (m / a) := by
  have hr : (1 / 4 : ℝ) ≤ (a + 1) / m := (le_div_iff₀ hm).mpr (by linarith)
  have hl : Real.log 2 ≤ Real.log (m / a) :=
    Real.log_le_log (by norm_num) ((le_div_iff₀ ha).mpr (by linarith))
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hp := mul_le_mul hr hl hlog (by positivity : 0 ≤ (a + 1) / m)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hp

end SRWTightness
