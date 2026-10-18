import SRWTightness.SourceUpperMarkParameters

open Filter
open scoped Topology
namespace SRWTightness

/-- The exact floored fine scale gives an inverse-t envelope for the terminal ratio. -/
theorem source_upper_fine_ratio_bound (t : ℝ) (ht : 0 < t) (hlog : 1 ≤ Real.log t) :
    t * upperTerminalFineRadius (sourceUpperLogRadius t) / sourceUpperRadius t ≤ 1 / t := by
  have hp : Real.log t ≤ (Real.log t) ^ 4 := by
    nlinarith [sq_nonneg (Real.log t - 1), sq_nonneg ((Real.log t) ^ 2 - 1)]
  have hexp : 2 * Real.log t + sourceUpperLogRadius t / 4 ≤ sourceUpperLogRadius t := by
    unfold sourceUpperLogRadius
    nlinarith
  have he := Real.exp_le_exp.mpr hexp
  have heq : Real.exp (2 * Real.log t) = t ^ 2 := by
    rw [show 2 * Real.log t = Real.log t + Real.log t by ring,
      Real.exp_add, Real.exp_log ht]
    ring
  rw [Real.exp_add, heq] at he
  have hr : upperTerminalFineRadius (sourceUpperLogRadius t) ≤
      Real.exp (sourceUpperLogRadius t / 4) := Nat.floor_le (Real.exp_pos _).le
  have hh := (mul_le_mul_of_nonneg_left hr (sq_nonneg t)).trans he
  have hm : 0 < sourceUpperRadius t := Real.exp_pos _
  apply (div_le_div_iff₀ hm ht).mpr
  change t * upperTerminalFineRadius (sourceUpperLogRadius t) * t ≤
    1 * Real.exp (sourceUpperLogRadius t)
  nlinarith

/-- The actual terminal fine-to-outer ratio, multiplied by t, tends to zero. -/
theorem source_upper_fine_ratio_limit :
    Tendsto (fun t : ℝ ↦
      t * upperTerminalFineRadius (sourceUpperLogRadius t) / sourceUpperRadius t)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ ↦ 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0))
  apply squeeze_zero' _ _ hi
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    unfold upperTerminalFineRadius sourceUpperRadius
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with t ht
    have ht0 : 0 < t := (Real.exp_pos _).trans_le ht
    have hl := Real.log_le_log (Real.exp_pos 1) ht
    rw [Real.log_exp] at hl
    exact source_upper_fine_ratio_bound t ht0 hl

end SRWTightness
