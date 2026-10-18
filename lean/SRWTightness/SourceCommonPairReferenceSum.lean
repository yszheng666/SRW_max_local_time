import SRWTightness.SourceCommonPairWeightedSum
import SRWTightness.SourceCommonPairSquareError
import SRWTightness.SourceCommonPairGWCoefficient
import SRWTightness.SourceCommonPairTiltEstimate

open MeasureTheory Filter
open scoped BigOperators

namespace SRWTightness

/-- The complete positive-endpoint reference sum has the manuscript quadratic exponent and t² factor. -/
theorem source_common_pair_reference_sum
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w → 20 ≤ j →
      20 ≤ sourceTotalTime t - (j : ℝ) →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ a : ℝ, 1 ≤ a → 2 * a ≤ sourceCommonPairInnerRadius t j →
      ∀ (K : Finset Site) (hpair : ({b, w} : Finset Site) ⊆ K),
      K ⊆ translateFinset b (diskFinset a) →
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤
        Real.log (sourceCommonPairInnerRadius t j) - Real.log a →
      (∑ k ∈ commonPairPositiveEndpoints (sourceCommonPairEndpoint t j),
        (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} *
        (markProductLaw (sourceCommonPairDomain t b j) K (sourceCommonPairIntensity t j) k).real
          {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * (sourceTerminalHeight t) ^ 2 / 2 ≤
            (sumMarks K k Y ⟨v, hpair v.property⟩ : ℝ)}) ≤
        C * t ^ 2 * Real.exp (-(sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
          (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 / sourceCommonPairRowScale t b w j) := by
  let C : ℝ := 33 * Real.exp (12 + 25 / (2 * (2 / Real.pi)))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [source_common_pair_gw_coefficient_pos, source_common_pair_tilt_estimate,
    source_common_pair_endpoint_interval, source_common_pair_level_range,
    source_common_pair_row_ge_remaining, source_common_pair_endpoint_error_uniform 1 (by norm_num),
    eventually_ge_atTop (sourceScaleThreshold 4), eventually_ge_atTop (2 * sourceTotalTimeError)]
    with t hc hw hi hl hr he ht htE
  intro b w j hbw hj hd hindex hdepth a ha hma K hpair hK hlog
  have htime := hl j hdepth
  have hv := hi j (by omega) htime.1 (by linarith) hdepth
  have hD := hr b w j hbw hindex hdepth
  have hm := ((sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1).trans
    (sourceCommonPairInnerRadius_ge_lower t j hdepth)
  have hcoeff := (hc b w j hbw hj hd hindex hdepth).le
  have hcost := (hw b w j hbw (by omega) hindex hdepth).2.2.2
  have herr := (he j htime.1 (by linarith) hv.1.le hdepth).le
  have hsquare := source_common_pair_square_error t b w j ht htE hm hv.1.le
    (by linarith) hD hv.2.2.le herr
  have hqbound := source_common_pair_endpoint_linear t j ht htE htime.1 (by linarith) hv.1.le
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hsum := source_common_pair_weighted_sum hGW hOcc hRes t b w j hbw a ha hma hm
    K hpair hK hlog (by omega) (sourceTerminalHeight t) (by linarith) hv.1 hv.2.2
    (by linarith) ((le_abs_self _).trans hqbound) hcoeff
  apply hsum.trans
  calc
    _ ≤ 33 * t ^ 2 * Real.exp ((12 + 25 / (2 * (2 / Real.pi))) +
        (-(sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
          (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 / sourceCommonPairRowScale t b w j)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      simp only [neg_div] at hsquare ⊢
      linarith only [hsquare, hcost]
    _ = _ := by rw [Real.exp_add]; dsimp [C]; ring

end SRWTightness
