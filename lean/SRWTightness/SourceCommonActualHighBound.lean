import SRWTightness.SourceCommonActualHighInclusion
import SRWTightness.SourceCommonActualGeometry
import SRWTightness.SourceCommonOriginHighBound

open MeasureTheory Filter
open scoped ENNReal
namespace SRWTightness

/-- The original walk has one root, the common prefix barrier, and two high local times. -/
def sourceCommonActualHighEvent (t : ℝ) (b w : Site) (j : ℕ) : Set Sample :=
  {ω | sourceActualCount t b 0 ω = 1 ∧
    (∀ i : ℕ, 0 < i → i ≤ j →
      Real.sqrt (2 * (sourceActualCount t b i ω : ℝ)) ≤ sourceCommonPairEndpoint t i) ∧
    ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * (sourceTerminalHeight t) ^ 2 / 2 ≤
      (domainLocalTime (diskFinset (Real.exp t)) 0 v ω : ℝ)}

/-- The common-prefix two-point bound applies to the original SRW local-time event. -/
theorem source_common_actual_high_upper (hpot : PotentialKernelAsymptoticInput)
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      sourceCoarseLowerLevel t ≤ j → 1 ≤ Real.sqrt (normSq (w - b)) →
      Real.sqrt (normSq (w - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 →
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
  obtain ⟨C, hC, hu⟩ := source_common_origin_high_upper hpot hGW hOcc hRes
  refine ⟨C, hC, ?_⟩
  filter_upwards [hu, source_common_actual_geometry] with t ht hg
  intro b w j hbw hcut hρ houter hi hd hlo hhi
  dsimp only
  intro inst₁ inst₂ inst₃ inst₄ inst₅ inst₆ hinput
  have hpair := source_common_pair_observation_contains b w (by linarith :
    0 < Real.sqrt (normSq (w - b)))
  have hupper := ht b w j hbw hcut hρ houter hi hd hlo hhi hinput hpair
  apply le_trans (measure_mono_ae ?_) hupper
  filter_upwards [domainExit_ne_top_ae (diskFinset (Real.exp t)) 0] with ω hfin
  intro hω
  obtain ⟨hm, hK, hroot⟩ := hg b w j hbw hi hd hlo hhi
  exact source_common_actual_high_inclusion t b w j hpair ω hm hK hroot hfin
    hω.1 hω.2.1 hω.2.2

end SRWTightness
