import SRWTightness.SourceCommonPairRemainingLarge
import SRWTightness.SourceCommonPairCoarseReferenceSum

open Filter
namespace SRWTightness

/-- The remaining time exceeds the real lower coarse cutoff uniformly in the source range. -/
theorem source_common_remaining_cutoff :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ,
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      (1000 * Real.log t) ^ (5 / 2 : ℝ) ≤ sourceTotalTime t - (j : ℝ) := by
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (sourceScaleThreshold 4),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (sourceTotalTimeError + 1))]
    with t ht hs hl
  intro j hd
  have hE := sourceTotalTimeError_pos
  have hl1 : 1 ≤ Real.log t := by linarith
  have hm := sourceLowerRadius_pos t
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by
    have hh := (hT t ht).2
    nlinarith [Real.exp_one_gt_two]
  have hi := (source_common_pair_inner_log_time t j hscale).2
  have hmi := Real.log_le_log hm (sourceCommonPairInnerRadius_ge_lower t j hd)
  have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1000 * Real.log t)
    (by norm_num : (1 : ℝ) ≤ 5 / 2)
  rw [Real.rpow_one] at hp
  have htwo := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (1 : ℝ) ≤ 5 / 2)
  rw [Real.rpow_one] at htwo
  have hgrowth : 2 * (1000 * Real.log t) ^ (5 / 2 : ℝ) ≤ Real.log (sourceLowerRadius t) := by
    rw [log_sourceLowerRadius, sourceLowerLogRadius,
      show 2000 * Real.log t = 2 * (1000 * Real.log t) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ 1000 * Real.log t)]
    exact mul_le_mul_of_nonneg_right htwo (by positivity)
  have htime := (abs_le.mp (sourceTotalTime_error t hs)).1
  have hc : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  linarith

/-- Every permitted later common level has the full 1000 log t barrier dent. -/
theorem source_common_dent_lower :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, sourceCoarseLowerLevel t ≤ j →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      1000 * Real.log t ≤ (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) := by
  filter_upwards [source_common_remaining_cutoff,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with t hr ht
  intro j hj hd
  have hjc : (1000 * Real.log t) ^ (5 / 2 : ℝ) ≤ (j : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hj)
  have hmin := le_min hjc (hr j hd)
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (1000 * Real.log t) ^ (5 / 2 : ℝ))
    hmin (by norm_num : (0 : ℝ) ≤ 2 / 5)
  rw [← Real.rpow_mul (by linarith : 0 ≤ 1000 * Real.log t)] at hh
  norm_num at hh
  exact hh

end SRWTightness
