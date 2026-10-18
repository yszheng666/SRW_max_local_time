import SRWTightness.SourceCommonActualHighBound
import SRWTightness.SourceCommonDistanceRange

open MeasureTheory Filter
open scoped ENNReal
namespace SRWTightness

/-- Equation (9.11) on the actual walk, with all pair-distance premises discharged. -/
theorem source_common_high_estimate (hpot : PotentialKernelAsymptoticInput)
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      sourceCoarseLowerLevel t ≤ j →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      let K := sourceCommonPairObservation b w
      ∀ [MeasurableSpace (List (Mark K))] [MeasurableSingletonClass (List (Mark K))]
        [MeasurableSpace (FiniteExcursionRecord (Mark K) j)]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) j)]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) j))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) j))],
      MarkedGWJointInput (Mark K) →
      pathLaw (sourceCommonActualHighEvent t b w j) ≤
      ENNReal.ofReal (C * t ^ 2 * Real.exp
        (-(sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
          (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 /
            sourceCommonPairRowScale t b w j)) := by
  obtain ⟨C, hC, hu⟩ := source_common_actual_high_upper hpot hGW hOcc hRes
  refine ⟨C, hC, ?_⟩
  filter_upwards [hu] with t ht
  intro b w j hbw hcut hi hd hlo hhi
  obtain ⟨hρ, houter⟩ := source_common_distance_range t b w j hbw hi
  exact ht b w j hbw hcut hρ houter hi hd hlo hhi

end SRWTightness
