import SRWTightness.SourceCommonPairRowTimeUniform
import SRWTightness.LatticeNorm

open Filter

namespace SRWTightness

/-- Manuscript (9.8): a uniform row-scale error for distinct sites at the actual common level. -/
theorem source_common_pair_row_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      |sourceCommonPairRowScale t b w j - (t - (j : ℝ) + (sourceCommonPairGap t : ℝ))| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := source_common_pair_row_time_uniform
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with t ht
  intro b w j hbw hj hdepth
  let ρ := Real.sqrt (normSq (w - b))
  have hρ : 1 ≤ ρ := by
    have hn := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    have hs := Real.sq_sqrt (normSq_nonneg (w - b))
    have hp := Real.sqrt_nonneg (normSq (w - b))
    dsimp [ρ]
    nlinarith
  have hρ0 : 0 < ρ := by linarith
  let r := sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0
  have hr : 0 < r := by
    dsimp [r, sourceRecordRadius]
    exact mul_pos (sourceLowerRadius_pos t) (Real.exp_pos _)
  have hindex : 1 ≤ sourceCommonPairDistanceIndex t ρ := by
    have hgap : 5 ≤ sourceCommonPairGap t := by unfold sourceCommonPairGap; omega
    change j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ at hj
    omega
  have hlog : 1 ≤ Real.log (r / ρ) := (Nat.one_le_floor_iff _).mp hindex
  have he := Real.exp_le_exp.mpr (show 0 ≤ Real.log (r / ρ) by linarith)
  rw [Real.exp_zero, Real.exp_log (div_pos hr hρ0)] at he
  have houter : ρ ≤ r := (one_le_div hρ0).mp he
  exact ht b w j hρ houter hj hdepth

end SRWTightness
