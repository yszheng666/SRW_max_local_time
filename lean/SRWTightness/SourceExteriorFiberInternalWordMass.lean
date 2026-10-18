import SRWTightness.SourceExteriorFiber
import SRWTightness.StoppedWordProbabilityInternal

open Filter
namespace SRWTightness

/-- The source exterior-fiber formula using the internally proved stopped-word cylinder mass. -/
theorem source_exterior_word_fiber_internal_word_mass (hF : ExteriorBridgeFactorizationInput)
    :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      let D := diskFinset (Real.exp t)
      let label := twoDomainExteriorLabel (K w)
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | killedExteriorRecord D (K b ∪ K w) (C b ∪ C w) label 0 ω = h} →
      ∀ us : List PathWord, us.length = h.1.length →
      (∀ p ∈ h.1.zip us, AdmissibleExitWord
        (if p.1.2.1 then C w else C b) p.1.2.2.1 p.1.2.2.2 p.2) →
      pathLaw.real {ω | killedChildRecords D (K b ∪ K w) (C b ∪ C w) 0 (fun _ u ↦ u) ω = us ∧
        killedExteriorRecord D (K b ∪ K w) (C b ∪ C w) label 0 ω = h} /
        pathLaw.real {ω | killedExteriorRecord D (K b ∪ K w) (C b ∪ C w) label 0 ω = h} =
          ((h.1.zip us).map (fun p ↦ (1 / 4 : ℝ) ^ p.2.length /
            traceExitProbability (if p.1.2.1 then C w else C b) p.1.2.2.1 p.1.2.2.2)).prod := by
  exact source_exterior_word_fiber hF stoppedWordProbabilityInput_internal

end SRWTightness
