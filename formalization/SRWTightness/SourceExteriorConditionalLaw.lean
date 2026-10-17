import SRWTightness.ExteriorConditionalWordLaw
import SRWTightness.SourceExteriorEntranceShell

open MeasureTheory Filter
namespace SRWTightness

/-- On the actual source geometry, conditioning on the exterior record leaves the exact ordered
product law of the selected component bridges for all complete internal words. -/
theorem source_exterior_conditional_word_law (hF : ExteriorBridgeFactorizationInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      (ProbabilityTheory.cond pathLaw {ω | sourcePairExteriorRecord t b w ν J ω = h}).map
        (killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w)
          0 (fun _ u ↦ u)) = exteriorIndependentWordLaw (C b) (C w) h := by
  filter_upwards [source_exterior_geometry] with t ht
  intro b w ν J hb hw hbw hd hν hform
  dsimp only
  intro h hh
  obtain ⟨hK₀, hK₁, hCD, hgap₀, hgap₁, _⟩ := ht b w ν J hb hw hbw hd hν hform
  exact exterior_conditional_word_law hF _ _ _ _ _ 0 hK₀ hK₁ hCD hgap₀ hgap₁ h hh

end SRWTightness
