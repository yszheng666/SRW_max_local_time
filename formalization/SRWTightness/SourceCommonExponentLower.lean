import SRWTightness.SourceCommonQuadraticLower
import SRWTightness.CommonRemainingRefined
import SRWTightness.SourceCommonRemainingLogSquare
import SRWTightness.SourceCommonPairRowLower

open Filter
namespace SRWTightness

/-- Equation (9.13): the complete common quadratic exponent dominates the spatial counting exponent. -/
theorem source_common_exponent_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w → 1 ≤ j →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      4 * t - 2 * (j : ℝ) +
        2 * (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) -
        4 * Real.log t - 4 * (sourceCommonPairGap t : ℝ) - C ≤
      sourceCommonPairEndpoint t j ^ 2 / (2 * ((j : ℝ) + 1)) +
        (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 /
          sourceCommonPairRowScale t b w j := by
  obtain ⟨B, hB, hb⟩ := source_common_quadratic_lower
  obtain ⟨E, hE, he⟩ := source_common_pair_row_estimate
  have hEt := sourceTotalTimeError_pos
  refine ⟨B + 4 * (E + sourceTotalTimeError) + 55, by positivity, ?_⟩
  filter_upwards [hb, he, source_common_pair_row_ge_remaining, source_common_remaining_log_square,
    source_common_barrier_slope, source_common_pair_level_range, sourceBarrierSlope_eventually_ge_one,
    eventually_ge_atTop (sourceScaleThreshold 4), Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (E + sourceTotalTimeError + 7))]
    with t hb he hrow hsquare hslope hr hθ1 ht hlog
  intro b w j hbw hj hi hd
  let d := sourceTotalTime t - (j : ℝ)
  let v := (min (j : ℝ) d) ^ (2 / 5 : ℝ)
  let δ := (sourceCommonPairGap t : ℝ) + E + sourceTotalTimeError
  have hd6 : 6 ≤ d := (hr j hd).2
  have hd0 : 0 < d := by linarith
  have hT0 : 0 < sourceTotalTime t := by
    dsimp [d] at hd6
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hD : d ≤ sourceCommonPairRowScale t b w j := hrow b w j hbw hi hd
  have hrowhi := (abs_le.mp (he b w j hbw hi hd)).2
  have htime := (abs_le.mp (sourceTotalTime_error t ht)).1
  have hδ : sourceCommonPairRowScale t b w j - d ≤ δ := by dsimp [d, δ]; linarith
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hgap := (sourceCommonPairGap_bounds t (by linarith)).2
  have hδl : δ ≤ 11 * Real.log t := by dsimp [δ]; linarith
  have hl1 : 1 ≤ Real.log t := by linarith
  have hv0 : 0 ≤ v := Real.rpow_nonneg (le_min (Nat.cast_nonneg _) hd0.le) _
  have hvpow : v ≤ d ^ (2 / 5 : ℝ) := Real.rpow_le_rpow
    (le_min (Nat.cast_nonneg _) hd0.le) (min_le_right _ _) (by norm_num)
  have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ d)
    (by norm_num : (2 / 5 : ℝ) ≤ 1)
  rw [Real.rpow_one] at hp
  have hvd := hvpow.trans hp
  have hδv := common_log_dent_ratio (Real.log t) d δ v hl1 (hsquare j hd) hδ0 hδl hvpow
  have hθ2 := (hslope j hd).2.1
  have hy : sourceBarrierSlope t * sourceTotalTime t = sourceTerminalHeight t :=
    div_mul_cancel₀ _ hT0.ne'
  have ha : 0 ≤ sourceTerminalHeight t - sourceCommonPairEndpoint t j := by
    have hh := source_common_pair_endpoint_gap_lower t j hθ1 (by dsimp [d] at hd6; linarith) hT0.ne'
    dsimp [d] at hd6
    linarith
  have hahi : sourceTerminalHeight t - sourceCommonPairEndpoint t j ≤ 2 * d + v := by
    have hh := mul_le_mul_of_nonneg_right hθ2 hd0.le
    change sourceTerminalHeight t - (4 + sourceBarrierSlope t * j - v) ≤ 2 * d + v
    dsimp only [d] at hh ⊢
    nlinarith
  have hden := common_remaining_refined_loss (sourceTerminalHeight t - sourceCommonPairEndpoint t j)
    d (sourceCommonPairRowScale t b w j) δ v 11 hd0 hD hδ ha hahi hv0 hvd hδv
  have hbase := hb j hj hd
  dsimp [d, δ, v] at hden
  linarith

end SRWTightness
