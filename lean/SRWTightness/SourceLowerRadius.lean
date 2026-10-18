import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace SRWTightness

/-- The exact lower-construction logarithmic radius D_- from (5.1). -/
noncomputable def sourceLowerLogRadius (t : ℝ) : ℝ := (2000 * Real.log t) ^ (5 / 2 : ℝ)

noncomputable def sourceLowerRadius (t : ℝ) : ℝ := Real.exp (sourceLowerLogRadius t)

@[simp] theorem sourceLowerRadius_pos (t : ℝ) : 0 < sourceLowerRadius t := Real.exp_pos _

@[simp] theorem log_sourceLowerRadius (t : ℝ) :
    Real.log (sourceLowerRadius t) = sourceLowerLogRadius t := Real.log_exp _

theorem sourceLowerLogRadius_ge_seven_log (t : ℝ) (ht : 1 ≤ Real.log t) :
    7 * Real.log t ≤ sourceLowerLogRadius t := by
  have hx : 1 ≤ 2000 * Real.log t := by linarith
  have hh := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (2 : ℝ) ≤ 5 / 2)
  rw [Real.rpow_two] at hh
  unfold sourceLowerLogRadius
  nlinarith [sq_nonneg (Real.log t - 1)]

/-- The geometric-scale cutoff is nonempty for an explicit sufficiently large t. -/
theorem sourceLowerRadius_cutoff_nonempty (t A : ℝ) (ht0 : 0 < t) (hA : 0 < A)
    (ht : 1 ≤ Real.log t) (hlogA : Real.log A ≤ Real.log t) :
    A ≤ sourceLowerRadius t / t ^ 6 := by
  have hD := sourceLowerLogRadius_ge_seven_log t ht
  have hlog : Real.log (A * t ^ 6) ≤ sourceLowerLogRadius t := by
    rw [Real.log_mul hA.ne' (pow_ne_zero _ ht0.ne'), Real.log_pow]
    norm_num
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity : 0 < A * t ^ 6)] at hexp
  exact (le_div_iff₀ (by positivity : 0 < t ^ 6)).mpr hexp

end SRWTightness
