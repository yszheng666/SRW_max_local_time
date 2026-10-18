import SRWTightness.SourceReferenceIntensityError
import SRWTightness.SourceLowerTimeGrowth
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Filter
open scoped Topology

namespace SRWTightness

theorem sourceLowerRadius_ge_self (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t) :
    t ≤ sourceLowerRadius t := by
  have hl := sourceScaleThreshold_log_lower 4 t ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hD := sourceLowerLogRadius_ge_seven_log t hl
  have hh := Real.exp_le_exp.mpr (show Real.log t ≤ sourceLowerLogRadius t by linarith)
  rwa [Real.exp_log (by linarith : 0 < t)] at hh

theorem sourceLowerRadius_tendsto_atTop : Tendsto sourceLowerRadius atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
  exact sourceLowerRadius_ge_self t ht

/-- The original source profile satisfies the explicit O(1/m) bound. -/
theorem sourceReferenceIntensity_profile_error (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t) :
    |sourceReferenceIntensity (sourceLowerRadius t) 14 - (2 / Real.pi)| ≤
      (56 * (2 / Real.pi)) / sourceLowerRadius t := by
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1
  exact sourceReferenceIntensity_fourteen_error _ hm

theorem sourceReferenceIntensity_profile_tendsto :
    Tendsto (fun t : ℝ ↦ sourceReferenceIntensity (sourceLowerRadius t) 14) atTop
      (𝓝 (2 / Real.pi)) := by
  have hlim : Tendsto (fun t : ℝ ↦ (56 * (2 / Real.pi)) / sourceLowerRadius t) atTop (𝓝 0) := by
    have hh := (tendsto_inv_atTop_zero.comp sourceLowerRadius_tendsto_atTop).const_mul
      (56 * (2 / Real.pi))
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using hh
  have hd : Tendsto (fun t : ℝ ↦ sourceReferenceIntensity (sourceLowerRadius t) 14 - (2 / Real.pi))
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hlim
    · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
      have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1
      exact (sourceReferenceIntensity_error _ 14 (sourceLowerRadius_pos t)
        (by norm_num) (by linarith)).1
    · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
      exact (le_abs_self _).trans (sourceReferenceIntensity_profile_error t ht)
  simpa using hd.add_const (2 / Real.pi)

theorem sourceReferenceIntensity_radius_tendsto :
    Tendsto (fun R : ℝ ↦ sourceReferenceIntensity (sourceLowerRadius (Real.log R)) 14)
      atTop (𝓝 (2 / Real.pi)) :=
  sourceReferenceIntensity_profile_tendsto.comp Real.tendsto_log_atTop

end SRWTightness
