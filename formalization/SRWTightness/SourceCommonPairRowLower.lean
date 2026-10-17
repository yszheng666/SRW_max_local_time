import SRWTightness.SourceCommonPairRowEstimate
import SRWTightness.SourceCoarseTime

open Filter

namespace SRWTightness

/-- The logarithmic gap eventually absorbs all fixed row-scale and total-time errors. -/
theorem source_common_pair_row_ge_remaining :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      sourceTotalTime t - (j : ℝ) ≤ sourceCommonPairRowScale t b w j := by
  obtain ⟨C, hC, hrow⟩ := source_common_pair_row_estimate
  filter_upwards [hrow, eventually_ge_atTop (sourceScaleThreshold 4),
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max 1 (C + sourceTotalTimeError)))] with t hr ht hl
  intro b w j hbw hj hdepth
  have hlog1 : 1 ≤ Real.log t := (le_max_left _ _).trans hl
  have hlogC : C + sourceTotalTimeError ≤ Real.log t := (le_max_right _ _).trans hl
  have hceil := Nat.le_ceil (10 * Real.log t)
  have hJ : C + sourceTotalTimeError ≤ (sourceCommonPairGap t : ℝ) := by
    simp only [sourceCommonPairGap, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hD := (abs_le.mp (hr b w j hbw hj hdepth)).1
  have hT := (abs_le.mp (sourceTotalTime_error t ht)).2
  linarith

end SRWTightness
