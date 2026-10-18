import SRWTightness.SourceCommonPairActualRowTime
import SRWTightness.SourceForestApplicationGeometry

open Filter

namespace SRWTightness

/-- A single constant controls the source common row scale uniformly for all sufficiently large t. -/
theorem source_common_pair_row_time_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ),
      1 ≤ Real.sqrt (normSq (w - b)) →
      Real.sqrt (normSq (w - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      |sourceCommonPairRowScale t b w j - (t - (j : ℝ) + (sourceCommonPairGap t : ℝ))| ≤ C := by
  let C := 2 * (diskGreenEnergyConstant / (2 / Real.pi) + Real.log 2) +
    1 / (2 / Real.pi) + Real.log 32 + 3
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hC : 0 < C := by
    have hE := div_pos diskGreenEnergyConstant_pos hg
    have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have h32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
    have hi : 0 < 1 / (2 / Real.pi : ℝ) := by positivity
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [eventually_ge_atTop T,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10 : ℝ))] with t ht hlog
  intro b w j hρ houter hj hdepth
  have hm := sourceLowerRadius_pos t
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by
    have hs := (hT t ht).2
    nlinarith [Real.exp_one_gt_two]
  exact source_common_pair_actual_row_time t b w j hlog hρ houter hj hscale hdepth

end SRWTightness
