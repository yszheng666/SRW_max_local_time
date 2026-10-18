import SRWTightness.SourceCommonDistanceRange
import SRWTightness.SourceCommonPairLogTime
import SRWTightness.SourceForestApplicationGeometry

open Filter
namespace SRWTightness

/-- A common endpoint index confines its two sites to the spatial counting radius. -/
theorem source_common_distance_upper :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      Real.sqrt (normSq (w - b)) ≤ Real.exp (t - (j : ℝ) - (sourceCommonPairGap t : ℝ)) := by
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [eventually_ge_atTop T] with t ht
  intro b w j hbw hi
  obtain ⟨hρ, houter⟩ := source_common_distance_range t b w j hbw hi
  have hρ0 : 0 < Real.sqrt (normSq (w - b)) := by linarith
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by
    have hh := (hT t ht).2
    nlinarith [Real.exp_one_gt_two, sourceLowerRadius_pos t]
  have hl := (source_common_pair_log_separation t _ hρ0 houter j (sourceCommonPairGap t) hi).1
  have hr := (source_common_pair_inner_log_time t j hscale).2
  have h32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hh : Real.log (Real.sqrt (normSq (w - b))) ≤
      t - (j : ℝ) - (sourceCommonPairGap t : ℝ) := by linarith
  simpa only [Real.exp_log hρ0] using Real.exp_le_exp.mpr hh

end SRWTightness
