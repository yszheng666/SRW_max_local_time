import SRWTightness.SourceUpperRootCap
import SRWTightness.LogPowerDomination

open Filter MeasureTheory
open scoped Topology

namespace SRWTightness

/-- The explicit root cap probability majorant vanishes. -/
theorem source_upper_root_cap_majorant_vanishes :
    Tendsto (fun t : ℝ ↦ 25 * Real.exp (2 * t - t ^ 2 / (4 * Real.log t)))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ ↦ 25 * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 25
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall (fun t ↦ by positivity)
  · filter_upwards [affine_log_eventually_le_rpow 12 0 1 1 (by norm_num) (by norm_num),
      eventually_gt_atTop (1 : ℝ)] with t ht ht1
    have ht0 : 0 < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos ht1
    have h : 12 * Real.log t ≤ t := by simpa using ht
    have hq : 3 * t ≤ t ^ 2 / (4 * Real.log t) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right h ht0.le]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

/-- The probability of any actual source upper block exceeding the root cap tends to zero. -/
theorem source_upper_root_cap_vanishes (hinput : PotentialKernelAsymptoticInput) :
    Tendsto (fun t : ℝ ↦ pathLaw.real (sourceUpperRootCapEvent t)) atTop (𝓝 0) := by
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ measureReal_nonneg))
    (source_upper_root_cap_probability hinput) source_upper_root_cap_majorant_vanishes

/-- The same actual root cap probability vanishes in the source radius parameter. -/
theorem source_upper_root_cap_radius_vanishes (hinput : PotentialKernelAsymptoticInput) :
    Tendsto (fun R : ℝ ↦ pathLaw.real (sourceUpperRootCapEvent (Real.log R)))
      atTop (𝓝 0) :=
  (source_upper_root_cap_vanishes hinput).comp Real.tendsto_log_atTop

end SRWTightness
