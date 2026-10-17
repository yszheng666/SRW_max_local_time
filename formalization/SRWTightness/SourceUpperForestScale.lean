import SRWTightness.SourceUpperBlockScales
import SRWTightness.LogPowerDomination

open Filter
open scoped Topology

namespace SRWTightness

/-- The exact floored observation radius has the source exponential ratio. -/
theorem source_upper_fine_exponential_ratio (t : ℝ) :
    upperTerminalFineRadius (sourceUpperLogRadius t) / sourceUpperRadius t ≤
      Real.exp (-3 * sourceUpperLogRadius t / 4) := by
  have hr := Nat.floor_le (Real.exp_pos (sourceUpperLogRadius t / 4)).le
  calc
    _ ≤ Real.exp (sourceUpperLogRadius t / 4) / Real.exp (sourceUpperLogRadius t) :=
      div_le_div_of_nonneg_right hr (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

/-- The source upper forest error scale tends to zero without an external scale premise. -/
theorem source_upper_forest_scale_vanishes :
    Tendsto (fun t : ℝ ↦ t ^ 2 * sourceUpperLogRadius t *
      Real.exp (-3 * sourceUpperLogRadius t / 4)) atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ ↦ 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0))
  apply squeeze_zero' _ _ hi
  · exact Filter.Eventually.of_forall (fun t ↦ by unfold sourceUpperLogRadius; positivity)
  · have hlogD := sourceUpperLogRadius_tendsto.eventually
      (affine_log_eventually_le_rpow 1 0 (1 / 4) 1 (by norm_num) (by norm_num))
    filter_upwards [hlogD, sourceUpperLogRadius_eventually 1,
      eventually_ge_atTop (Real.exp 1)] with t hd hD ht
    have ht0 : 0 < t := (Real.exp_pos _).trans_le ht
    have hl : 1 ≤ Real.log t := by
      have h := Real.log_le_log (Real.exp_pos 1) ht
      simpa only [Real.log_exp] using h
    have hp : Real.log t ≤ (Real.log t) ^ 4 := by
      nlinarith [sq_nonneg (Real.log t - 1), sq_nonneg ((Real.log t) ^ 2 - 1)]
    have hDlog : 3 * Real.log t ≤ sourceUpperLogRadius t / 2 := by
      unfold sourceUpperLogRadius
      nlinarith
    have hd' : Real.log (sourceUpperLogRadius t) ≤ sourceUpperLogRadius t / 4 := by
      simpa only [one_mul, add_zero, Real.rpow_one, one_div_mul_eq_div] using hd
    calc
      _ = Real.exp (2 * Real.log t + Real.log (sourceUpperLogRadius t) -
          3 * sourceUpperLogRadius t / 4) := by
        rw [show -3 * sourceUpperLogRadius t / 4 =
          -(3 * sourceUpperLogRadius t / 4) by ring, Real.exp_neg,
          Real.exp_sub, Real.exp_add, show 2 * Real.log t =
          Real.log t + Real.log t by ring, Real.exp_add, Real.exp_log ht0,
          Real.exp_log (by linarith : 0 < sourceUpperLogRadius t)]
        ring
      _ ≤ Real.exp (-Real.log t) := Real.exp_le_exp.mpr (by linarith only [hd', hDlog])
      _ = 1 / t := by rw [Real.exp_neg, Real.exp_log ht0, one_div]

end SRWTightness
