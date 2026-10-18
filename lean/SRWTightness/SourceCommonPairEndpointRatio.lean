import SRWTightness.SourceCommonPairEndpointPositive

open Filter

namespace SRWTightness

/-- The actual barrier slope eventually lies in a fixed narrow interval around two. -/
theorem sourceBarrierSlope_eventually_band :
    ∀ᶠ t : ℝ in atTop, (7 / 4 : ℝ) ≤ sourceBarrierSlope t ∧ sourceBarrierSlope t ≤ 9 / 4 := by
  have he := (tendsto_order.1 sourceBarrierSlope_weighted_tendsto_zero).2 (1 / 4) (by norm_num)
  filter_upwards [he, eventually_ge_atTop (sourceScaleThreshold 4)] with t he ht
  have hd := sourceLowerTime_ge_one t ht
  have hm : |sourceBarrierSlope t - 2| ≤
      |sourceBarrierSlope t - 2| * sourceLowerTime (sourceLowerRadius t) := by
    nlinarith [abs_nonneg (sourceBarrierSlope t - 2)]
  have hl := neg_abs_le (sourceBarrierSlope t - 2)
  have hu := le_abs_self (sourceBarrierSlope t - 2)
  constructor <;> linarith

/-- Coarse endpoints and their deficits have separated uniform ratios needed for GW weighting. -/
theorem source_common_pair_endpoint_ratios (t : ℝ) (j : ℕ)
    (hθ : (7 / 4 : ℝ) ≤ sourceBarrierSlope t ∧ sourceBarrierSlope t ≤ 9 / 4)
    (hj : 20 ≤ j) (hd : 20 ≤ sourceTotalTime t - (j : ℝ))
    (he : |sourceCommonPairScaledEndpoint t j - sourceCommonPairEndpoint t j| ≤ 1) :
    sourceCommonPairScaledEndpoint t j ≤ (5 / 2 : ℝ) * j ∧
      (3 / 2 : ℝ) * (sourceTotalTime t - (j : ℝ)) ≤
        sourceTerminalHeight t - sourceCommonPairScaledEndpoint t j := by
  have hj20 : (20 : ℝ) ≤ j := by exact_mod_cast hj
  have hT : sourceTotalTime t ≠ 0 := by linarith
  have hid : sourceBarrierSlope t * sourceTotalTime t = sourceTerminalHeight t :=
    div_mul_cancel₀ _ hT
  have hp : 0 ≤ (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) :=
    Real.rpow_nonneg (le_min (by linarith) (by linarith)) _
  have he' := (abs_le.mp he).2
  unfold sourceCommonPairEndpoint at he'
  have hu := mul_le_mul_of_nonneg_right hθ.2 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have hl := mul_le_mul_of_nonneg_right hθ.1 (by linarith : 0 ≤ sourceTotalTime t - j)
  constructor <;> nlinarith

end SRWTightness
