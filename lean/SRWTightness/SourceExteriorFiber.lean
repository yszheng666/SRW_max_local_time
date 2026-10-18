import SRWTightness.SourceExteriorGeometry
import SRWTightness.ExteriorWordFiber

open Filter
namespace SRWTightness

/-- Actual manuscript exterior records factor into the prescribed bridges of their labeled long balls. -/
theorem source_exterior_bridges (hF : ExteriorBridgeFactorizationInput) :
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
      pathLaw.real {ω | killedChildRecords D (K b ∪ K w) (C b ∪ C w) 0 (fun _ u ↦ u) ω = us ∧
        killedExteriorRecord D (K b ∪ K w) (C b ∪ C w) label 0 ω = h} /
        pathLaw.real {ω | killedExteriorRecord D (K b ∪ K w) (C b ∪ C w) label 0 ω = h} =
          labeledExteriorBridgeWordProduct (C b) (C w) h us := by
  filter_upwards [source_exterior_geometry] with t ht
  intro b w ν J hb hw hbw ha hν hform
  obtain ⟨hK₀, hK₁, hCD, hgap₀, hgap₁, _⟩ := ht b w ν J hb hw hbw ha hν hform
  dsimp only
  intro h hh us hlen
  exact exterior_two_domain_bridges hF _ _ _ _ _ 0 hK₀ hK₁ hCD hgap₀ hgap₁ h hh us hlen

/-- Equation exterior-fiber on the actual source geometry, for each admissible internal word tuple. -/
theorem source_exterior_word_fiber (hF : ExteriorBridgeFactorizationInput)
    (hW : StoppedWordProbabilityInput) :
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
  filter_upwards [source_exterior_geometry] with t ht
  intro b w ν J hb hw hbw ha hν hform
  obtain ⟨hK₀, hK₁, hCD, hgap₀, hgap₁, _⟩ := ht b w ν J hb hw hbw ha hν hform
  dsimp only
  intro h hh us hlen hu
  exact exterior_two_domain_word_fiber hF hW _ _ _ _ _ 0 hK₀ hK₁ hCD hgap₀ hgap₁
    h hh us hlen hu

end SRWTightness
