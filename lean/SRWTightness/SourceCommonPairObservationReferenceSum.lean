import SRWTightness.SourceCommonPairReferenceSum
import SRWTightness.SourceCommonPairObservationUniform
import SRWTightness.SourceCommonPairRemainingLarge

open MeasureTheory Filter
open scoped BigOperators

namespace SRWTightness

/-- Reference endpoint sum on the source's actual doubled-distance observation ball. -/
theorem source_common_pair_observation_reference_sum
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w → 20 ≤ j →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (hpair : ({b, w} : Finset Site) ⊆ sourceCommonPairObservation b w),
      (∑ k ∈ commonPairPositiveEndpoints (sourceCommonPairEndpoint t j),
        (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} *
        (markProductLaw (sourceCommonPairDomain t b j) (sourceCommonPairObservation b w) (sourceCommonPairIntensity t j) k).real
          {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * (sourceTerminalHeight t) ^ 2 / 2 ≤
            (sumMarks (sourceCommonPairObservation b w) k Y ⟨v, hpair v.property⟩ : ℝ)}) ≤
        C * t ^ 2 * Real.exp (-(sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
          (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 / sourceCommonPairRowScale t b w j) := by
  obtain ⟨C, hC, hbound⟩ := source_common_pair_reference_sum hGW hOcc hRes
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, source_common_pair_observation_uniform,
    source_common_pair_remaining_large 20] with t ht hgeom hremaining
  intro b w j hbw hj hindex hdepth hpair
  have hd := (hremaining j hdepth).2
  have hs := hgeom b w j hbw hindex
  exact ht b w j hbw hj hd hindex hdepth (2 * Real.sqrt (normSq (w - b)))
    hs.1 hs.2.1 (sourceCommonPairObservation b w) hpair (Finset.Subset.refl _) hs.2.2

end SRWTightness
