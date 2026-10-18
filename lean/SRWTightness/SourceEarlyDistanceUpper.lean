import SRWTightness.SourceCommonDistanceUpper

open Filter
namespace SRWTightness

/-- Every positive distance index confines its distinct sites to the required counting radius. -/
theorem source_early_distance_upper :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (a : ℕ), 1 ≤ a → b ≠ w →
      a = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      1 ≤ Real.sqrt (normSq (w - b)) ∧
        Real.sqrt (normSq (w - b)) ≤ Real.exp (t - (a : ℝ)) := by
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [eventually_ge_atTop T] with t ht
  intro b w a ha hbw hi
  let ρ := Real.sqrt (normSq (w - b))
  have hρ : 1 ≤ ρ := by
    have hn := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    have hs := Real.sq_sqrt (normSq_nonneg (w - b))
    have hp := Real.sqrt_nonneg (normSq (w - b))
    dsimp only [ρ]
    nlinarith only [hn, hs, hp]
  have hρ0 : 0 < ρ := by linarith only [hρ]
  let r := sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0
  have hr : 0 < r := mul_pos (sourceLowerRadius_pos t) (Real.exp_pos _)
  have hindex : 1 ≤ ⌊Real.log (r / ρ)⌋₊ := ha.trans_eq hi
  have hlog : 1 ≤ Real.log (r / ρ) := (Nat.one_le_floor_iff _).mp hindex
  have he := Real.exp_le_exp.mpr (show 0 ≤ Real.log (r / ρ) by linarith only [hlog])
  rw [Real.exp_zero, Real.exp_log (div_pos hr hρ0)] at he
  have houter : ρ ≤ r := (one_le_div hρ0).mp he
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by
    have hh := (hT t ht).2
    nlinarith [Real.exp_one_gt_two, sourceLowerRadius_pos t]
  have hl := (source_common_pair_log_separation t ρ hρ0 houter 0 a (by simpa using hi)).1
  have hu := (source_common_pair_inner_log_time t 0 hscale).2
  have h32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hh : Real.log ρ ≤ t - (a : ℝ) := by
    simp only [Nat.cast_zero, sub_zero] at hu
    linarith only [hl, hu, h32]
  refine ⟨hρ, ?_⟩
  simpa only [Real.exp_log hρ0] using Real.exp_le_exp.mpr hh

end SRWTightness
