import SRWTightness.SourceCommonPairRemainingLarge

open Filter
namespace SRWTightness

/-- The common remaining time dominates the square of log t uniformly in the source range. -/
theorem source_common_remaining_log_square :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ,
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      (Real.log t) ^ 2 ≤ sourceTotalTime t - (j : ℝ) := by
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
  have hp := Real.rpow_le_rpow_of_exponent_le
    (by linarith : 1 ≤ 2000 * Real.log t) (by norm_num : (2 : ℝ) ≤ 5 / 2)
  rw [Real.rpow_two] at hp
  have hgrowth : (2000 * Real.log t) ^ 2 ≤ Real.log (sourceLowerRadius t) := by
    rw [log_sourceLowerRadius]
    exact hp
  have htime := (abs_le.mp (sourceTotalTime_error t hs)).1
  have hc : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith [sq_nonneg (Real.log t - 1)]

end SRWTightness
