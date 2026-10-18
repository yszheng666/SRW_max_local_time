import SRWTightness.SourceCommonPairObservationGeometry
import SRWTightness.SourceCommonPairProjectedChernoff

open MeasureTheory

namespace SRWTightness

/-- The common observation ball has twice the actual pair distance as radius. -/
noncomputable def sourceCommonPairObservation (b w : Site) : Finset Site :=
  translateFinset b (diskFinset (2 * Real.sqrt (normSq (w - b))))

/-- The source two-site bound on the actual doubled-distance observation ball. -/
theorem source_common_pair_distance_chernoff
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (t : ℝ) (b w : Site) (hbw : b ≠ w)
    (hρ : 1 ≤ Real.sqrt (normSq (w - b)))
    (houter : Real.sqrt (normSq (w - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (hgap : sourceCommonPairGap t ≤
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))))
    (hJ : Real.log 4 + 1 ≤ (sourceCommonPairGap t : ℝ))
    (henergy : diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 +
      Real.log 2 + 1 ≤ (sourceCommonPairGap t : ℝ))
    (hm : 70 ≤ sourceCommonPairInnerRadius t
      (sourceCommonPairLevel t (Real.sqrt (normSq (w - b)))))
    (W : ℝ) (hW : 0 ≤ W)
    (hsmall : (2 / Real.pi) * sourceCommonPairRowScale t b w
      (sourceCommonPairLevel t (Real.sqrt (normSq (w - b)))) * W < 1)
    (u y : ℝ) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let j := sourceCommonPairLevel t (Real.sqrt (normSq (w - b)))
    let K := sourceCommonPairObservation b w
    let hpair := source_common_pair_observation_contains b w (by linarith :
      0 < Real.sqrt (normSq (w - b)))
    (markProductLaw (sourceCommonPairDomain t b j) K (sourceCommonPairIntensity t j) k).real
      {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * y ^ 2 / 2 ≤
        (sumMarks K k Y ⟨v, hpair v.property⟩ : ℝ)} ≤
      Real.exp (-(2 / Real.pi) * y ^ 2 * Real.log (1 + W) +
        sourceCommonPairIntensity t j * u ^ 2 * W /
          (1 - (2 / Real.pi) * sourceCommonPairRowScale t b w j * W)) := by
  have hpos : 0 < Real.sqrt (normSq (w - b)) := by linarith
  have hs := source_common_pair_observation_separation t _ hpos houter
    (sourceCommonPairLevel t _) (sourceCommonPairGap t)
    (sourceCommonPairLevel_add_gap t _ hgap) hJ henergy
  exact source_common_pair_projected_chernoff hOcc hRes t b w
    (sourceCommonPairLevel t _) hbw (2 * Real.sqrt (normSq (w - b))) (by linarith)
    hs.1 hm (sourceCommonPairObservation b w)
    (source_common_pair_observation_contains b w hpos) (Finset.Subset.refl _) hs.2
    W hW hsmall u y k hk

end SRWTightness
