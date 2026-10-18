import SRWTightness.SourceTerminalErrorSmall
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

namespace SRWTightness

/-- The source observation cutoff gives the sharp logarithmic terminal error rate uniformly in a. -/
theorem source_terminal_error_rate (W m a t : ℝ) (hW : 0 ≤ W) (hm : 0 < m)
    (ha : 1 ≤ a) (ht : Real.exp 1 ≤ t) (hcut : a ≤ m / t ^ 6) :
    W * (a + 1) / m * Real.log (m / a) ≤ 12 * W * Real.log t / t ^ 6 := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ht0 : 0 < t := by linarith
  have ha0 : 0 < a := by linarith
  have hpow : t ≤ t ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ t)
      (by norm_num : 1 ≤ 6)
  have hcut' := (le_div_iff₀ (pow_pos ht0 6)).mp hcut
  have hratio : t ^ 6 ≤ m / a := (le_div_iff₀ ha0).mpr (by nlinarith)
  have hlog : 0 ≤ Real.log (m / a) := Real.log_nonneg (by linarith)
  have hmono := Real.log_div_self_antitoneOn (ht.trans hpow)
    ((ht.trans hpow).trans hratio) hratio
  calc
    W * (a + 1) / m * Real.log (m / a) ≤ W * (2 * a) / m * Real.log (m / a) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hW) hm.le) hlog
    _ = 2 * W * (Real.log (m / a) / (m / a)) := by field_simp <;> ring
    _ ≤ 2 * W * (Real.log (t ^ 6) / t ^ 6) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = 12 * W * Real.log t / t ^ 6 := by rw [Real.log_pow]; ring

end SRWTightness
