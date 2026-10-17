import SRWTightness.CommonQuadraticLower
import SRWTightness.SourceCommonBarrierSlope
import SRWTightness.SourceCommonPairEndpointPositive

open Filter
namespace SRWTightness

/-- The source exponent already has its spatial lower bound with the exact remaining-time denominator. -/
theorem source_common_quadratic_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, 1 ≤ j →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      4 * t - 2 * (j : ℝ) +
        2 * (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) - 4 * Real.log t - C ≤
      sourceCommonPairEndpoint t j ^ 2 / (2 * ((j : ℝ) + 1)) +
        (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 /
          (sourceTotalTime t - j) := by
  have hE := sourceTotalTimeError_pos
  refine ⟨4 * sourceTotalTimeError + 27, by positivity, ?_⟩
  filter_upwards [source_common_barrier_slope, source_common_pair_level_range,
    sourceBarrierSlope_eventually_ge_one, eventually_ge_atTop (sourceScaleThreshold 4)]
    with t hs hr hθ1 ht
  intro j hj hd
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hrem := (hr j hd).2
  have hT0 : 0 < sourceTotalTime t := by linarith
  obtain ⟨hθ0, hθ2, herr⟩ := hs j hd
  let w := (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)
  have hw0 : 0 ≤ w := Real.rpow_nonneg
    (le_min (Nat.cast_nonneg _) (by linarith)) _
  have hw : 2 * w - 1 ≤ sourceBarrierSlope t * w := by
    have hh := mul_le_mul_of_nonneg_right (neg_abs_le (sourceBarrierSlope t - 2)) hw0
    change |sourceBarrierSlope t - 2| * w ≤ 1 at herr
    nlinarith
  have hy : sourceBarrierSlope t * sourceTotalTime t = 2 * t - Real.log t := by
    simp [sourceBarrierSlope, sourceTerminalHeight, hT0.ne']
  have he := (abs_le.mp (sourceTotalTime_error t ht)).2
  have hb := common_quadratic_lower t (sourceTotalTime t) (Real.log t) sourceTotalTimeError
    (sourceBarrierSlope t) (j : ℝ) w (by linarith) (by linarith) he hθ0 hθ2 hy hw
  have hq : sourceCommonPairEndpoint t j = sourceBarrierSlope t * j + (4 - w) := by
    dsimp [sourceCommonPairEndpoint, w]
    ring
  rw [← hq] at hb
  change _ ≤ sourceCommonPairEndpoint t j ^ 2 / (2 * (j : ℝ)) +
    (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 / (sourceTotalTime t - j) at hb
  have hq0 := sourceCommonPairEndpoint_ge_four t j hθ1 hj (by linarith)
  have hqhi : sourceCommonPairEndpoint t j ≤ 6 * j := by
    have hm := mul_le_mul_of_nonneg_right hθ2 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    rw [hq]
    linarith
  have hsq : sourceCommonPairEndpoint t j ^ 2 ≤ 36 * (j : ℝ) * (j + 1) := by
    nlinarith [sq_nonneg (6 * (j : ℝ) - sourceCommonPairEndpoint t j)]
  have hl := common_generation_denominator_loss (sourceCommonPairEndpoint t j) (j : ℝ) 36
    (by linarith) hsq
  dsimp only [w] at hb
  linarith

end SRWTightness
