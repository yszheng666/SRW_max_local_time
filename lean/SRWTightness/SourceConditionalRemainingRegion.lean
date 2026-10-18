import SRWTightness.SourceFineTupleActualForests
import SRWTightness.SourceConditionalPathSupport
import SRWTightness.SourceTupleRemainingRegion

open MeasureTheory Filter
open scoped BigOperators
namespace SRWTightness

/-- On each positive exterior atom, the actual remaining two forests with capped original root
counts place the actual fine tuple in the uniform comparison region, almost surely. -/
theorem source_conditional_remaining_region (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (A C a₀ a₁ : ℝ) (K₀ K₁ : Finset Site), 0 ≤ A → 0 ≤ C →
      1 ≤ a₀ → a₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ a₁ → a₁ ≤ sourceLowerRadius t / t ^ 6 →
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ k l : ℕ, k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      ∀ᵐ p ∂ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h},
      sourceActualCount t b ν p.1 = k → sourceActualCount t w ν p.1 = l →
      forestPopulationList _ (sourceActualFineForest t b K₀ ν p.1) ∈
        sourceContinuationBand t ν
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) →
      forestPopulationList _ (sourceActualFineForest t w K₁ ν p.1) ∈
        sourceContinuationBand t ν
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) →
      sourceFineTuple t b w K₀ K₁ ν J h p.1 ∈
        orderedTupleErrorRegion (fun i ↦ (h.1.get i).2.1) k l
          (fun r ↦ ∑ i, sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J (r i))
          (16 * ((ν : ℝ) + 1) ^ 2 *
            (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
              C * 15 / (sourceRecordRadius (sourceLowerRadius t)
                (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
            2 * sourceForestQuadraticError B W 8 t) := by
  filter_upwards [source_fine_tuple_actual_forests hExt hFlat,
    source_tuple_remaining_region B W hB hW] with t hforest hregion
  intro b w ν J hb hw hbw hd hν hform hdepth A C a₀ a₁ K₀ K₁ hA hC
    ha₀ hc₀ ha₁ hc₁ h hh k l hk hl
  have hs := source_conditional_path_support t b w ν J h _
    (hforest b w ν J hb hw hbw hd hν hform K₀ K₁ a₀ ha₀ hc₀ h hh)
  filter_upwards [hs] with p hp
  intro hx hy hb₀ hb₁
  obtain ⟨hcompat, hpair, hcount₀, hcount₁⟩ := hp
  apply hregion ν J hdepth A C a₀ a₁ K₀ K₁ hA hC ha₀ hc₀ ha₁ hc₁
    h.1.length (fun i ↦ (h.1.get i).2.1) _ k l hcompat
    (hcount₀.trans hx) (hcount₁.trans hy) hk hl
  · simpa only [hpair] using hb₀
  · simpa only [hpair] using hb₁

end SRWTightness
