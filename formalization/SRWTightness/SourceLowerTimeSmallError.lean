import SRWTightness.SourceLowerTimeGrowth
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Filter
open scoped Topology

namespace SRWTightness

noncomputable def sourceLowerTimeSmallQuantity (t : ℝ) : ℝ :=
  sourceLowerTime (sourceLowerRadius t) ^ 2 / t +
    sourceLowerTime (sourceLowerRadius t) * Real.log t / t

noncomputable def sourceLowerTimeMajorant (t : ℝ) : ℝ :=
  (4 * (2000 * Real.log t) ^ 6 + 4 * sourceLowerTimeError ^ 2 + Real.log t ^ 2) / t

theorem sourceLowerTimeSmallQuantity_bounds (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t) :
    0 ≤ sourceLowerTimeSmallQuantity t ∧ sourceLowerTimeSmallQuantity t ≤ sourceLowerTimeMajorant t := by
  have hb := sourceLowerTime_square_upper t ht
  have hl := sourceScaleThreshold_log_lower 4 t ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 ≤ t := by linarith
  have hcross : sourceLowerTime (sourceLowerRadius t) * Real.log t ≤
      sourceLowerTime (sourceLowerRadius t) ^ 2 + Real.log t ^ 2 := by
    nlinarith [sq_nonneg (sourceLowerTime (sourceLowerRadius t) - Real.log t),
      sq_nonneg (sourceLowerTime (sourceLowerRadius t)), sq_nonneg (Real.log t)]
  have hnum : sourceLowerTime (sourceLowerRadius t) ^ 2 +
      sourceLowerTime (sourceLowerRadius t) * Real.log t ≤
      4 * (2000 * Real.log t) ^ 6 + 4 * sourceLowerTimeError ^ 2 + Real.log t ^ 2 := by
    nlinarith [hb.2]
  constructor
  · unfold sourceLowerTimeSmallQuantity
    exact add_nonneg (div_nonneg (sq_nonneg _) ht0)
      (div_nonneg (mul_nonneg hb.1 (by linarith)) ht0)
  · have hh := div_le_div_of_nonneg_right hnum ht0
    simpa only [sourceLowerTimeSmallQuantity, sourceLowerTimeMajorant, add_div] using hh

theorem sourceLowerTimeMajorant_tendsto_zero :
    Tendsto sourceLowerTimeMajorant atTop (𝓝 0) := by
  have h6 : Tendsto (fun t : ℝ ↦ Real.log t ^ 6 / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero
  have h0 : Tendsto (fun t : ℝ ↦ 1 / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h2 : Tendsto (fun t : ℝ ↦ Real.log t ^ 2 / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hh := ((h6.const_mul (4 * (2000 : ℝ) ^ 6)).add
    (h0.const_mul (4 * sourceLowerTimeError ^ 2))).add h2
  have he : sourceLowerTimeMajorant = fun t : ℝ ↦
      (4 * (2000 : ℝ) ^ 6) * (Real.log t ^ 6 / t) +
        (4 * sourceLowerTimeError ^ 2) * (1 / t) + Real.log t ^ 2 / t := by
    funext t
    unfold sourceLowerTimeMajorant
    ring
  rw [he]
  simpa using hh

/-- Manuscript (5.2) for the actual Green-function d and exact lower-construction radius m(t). -/
theorem source_lower_time_small_error :
    Tendsto sourceLowerTimeSmallQuantity atTop (𝓝 0) := by
  apply squeeze_zero' _ _ sourceLowerTimeMajorant_tendsto_zero
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    exact (sourceLowerTimeSmallQuantity_bounds t ht).1
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    exact (sourceLowerTimeSmallQuantity_bounds t ht).2

theorem source_lower_time_small_error_at_radius :
    Tendsto (fun R : ℝ ↦ sourceLowerTimeSmallQuantity (Real.log R)) atTop (𝓝 0) :=
  source_lower_time_small_error.comp Real.tendsto_log_atTop

end SRWTightness
