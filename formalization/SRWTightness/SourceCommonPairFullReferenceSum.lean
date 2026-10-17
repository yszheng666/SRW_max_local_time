import SRWTightness.SourceCommonPairObservationReferenceSum
import SRWTightness.CommonPairZeroEndpoint
import SRWTightness.SourceCommonPairObservationUniform
import SRWTightness.SourceCommonPairRemainingLarge

open MeasureTheory Filter
open scoped BigOperators

namespace SRWTightness

/-- All permitted population states, including zero, obey the source reference estimate. -/
theorem source_common_pair_full_reference_sum
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w → 20 ≤ j →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (hpair : ({b, w} : Finset Site) ⊆ sourceCommonPairObservation b w),
      (∑ k ∈ Finset.range (⌊(sourceCommonPairEndpoint t j) ^ 2 / 2⌋₊ + 1),
        (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} *
        (markProductLaw (sourceCommonPairDomain t b j) (sourceCommonPairObservation b w) (sourceCommonPairIntensity t j) k).real
          {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * (sourceTerminalHeight t) ^ 2 / 2 ≤
            (sumMarks (sourceCommonPairObservation b w) k Y ⟨v, hpair v.property⟩ : ℝ)}) ≤
        C * t ^ 2 * Real.exp (-(sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
          (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 / sourceCommonPairRowScale t b w j) := by
  obtain ⟨C, hC, hbound⟩ := source_common_pair_observation_reference_sum hGW hOcc hRes
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  intro b w j hbw hj hindex hdepth hpair
  have ht0 : 0 < t := by linarith
  have hy : 0 < sourceTerminalHeight t := by
    unfold sourceTerminalHeight
    linarith [Real.log_le_sub_one_of_pos ht0]
  have hz := projected_mark_zero_high_probability (sourceCommonPairDomain t b j)
    (sourceCommonPairObservation b w) ({b, w} : Finset Site) hpair
    (by simp) (sourceCommonPairIntensity t j)
    ((2 / Real.pi) * (sourceTerminalHeight t) ^ 2 / 2) (by positivity)
  rw [common_pair_sum_include_zero _ _ (by rw [hz]; simp)]
  exact ht b w j hbw hj hindex hdepth hpair

end SRWTightness
