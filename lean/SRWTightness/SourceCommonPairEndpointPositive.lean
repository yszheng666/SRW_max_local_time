import SRWTightness.SourceCommonPairEndpoint
import SRWTightness.SourceBarrierSlopeError

open Filter

namespace SRWTightness

/-- The source barrier slope is eventually at least one. -/
theorem sourceBarrierSlope_eventually_ge_one :
    ∀ᶠ t : ℝ in atTop, 1 ≤ sourceBarrierSlope t := by
  have he := (tendsto_order.1 sourceBarrierSlope_weighted_tendsto_zero).2 1 (by norm_num)
  filter_upwards [he, eventually_ge_atTop (sourceScaleThreshold 4)] with t he ht
  have hd := sourceLowerTime_ge_one t ht
  have ha := abs_nonneg (sourceBarrierSlope t - 2)
  have hm : |sourceBarrierSlope t - 2| ≤
      |sourceBarrierSlope t - 2| * sourceLowerTime (sourceLowerRadius t) := by nlinarith
  have hl := neg_abs_le (sourceBarrierSlope t - 2)
  linarith

/-- The actual coarse barrier endpoint is positive at every nonzero permitted generation. -/
theorem sourceCommonPairEndpoint_ge_four (t : ℝ) (j : ℕ)
    (hθ : 1 ≤ sourceBarrierSlope t) (hj : 1 ≤ j) (hjT : (j : ℝ) ≤ sourceTotalTime t) :
    4 ≤ sourceCommonPairEndpoint t j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp := Real.rpow_le_rpow
    (le_min (Nat.cast_nonneg j : (0 : ℝ) ≤ j) (sub_nonneg.mpr hjT))
    (min_le_left (j : ℝ) (sourceTotalTime t - j)) (by norm_num : (0 : ℝ) ≤ 2 / 5)
  have hp' := Real.rpow_le_rpow_of_exponent_le hj1 (by norm_num : (2 / 5 : ℝ) ≤ 1)
  rw [Real.rpow_one] at hp'
  have hmul := mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  unfold sourceCommonPairEndpoint
  linarith

/-- The unscaled endpoint stays below the terminal height by the remaining time minus four. -/
theorem source_common_pair_endpoint_gap_lower (t : ℝ) (j : ℕ)
    (hθ : 1 ≤ sourceBarrierSlope t) (hjT : (j : ℝ) ≤ sourceTotalTime t)
    (hT : sourceTotalTime t ≠ 0) :
    sourceTotalTime t - (j : ℝ) - 4 ≤ sourceTerminalHeight t - sourceCommonPairEndpoint t j := by
  have he : sourceBarrierSlope t * sourceTotalTime t = sourceTerminalHeight t :=
    div_mul_cancel₀ _ hT
  have hm := mul_le_mul_of_nonneg_right hθ (sub_nonneg.mpr hjT)
  have hp : 0 ≤ (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) :=
    Real.rpow_nonneg (le_min (Nat.cast_nonneg _) (sub_nonneg.mpr hjT)) _
  unfold sourceCommonPairEndpoint
  nlinarith

end SRWTightness
