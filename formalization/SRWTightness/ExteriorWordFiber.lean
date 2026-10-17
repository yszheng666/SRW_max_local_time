import SRWTightness.ExteriorTwoDomainBridges
import SRWTightness.ExternalStoppedWordMass

namespace SRWTightness

/-- Literal finite-word weights in a two-domain exterior fiber, for admissible internal words. -/
theorem exterior_two_domain_word_fiber (hF : ExteriorBridgeFactorizationInput)
    (hW : StoppedWordProbabilityInput)
    (D K₀ K₁ C₀ C₁ : Finset Site) (x : Site)
    (hK₀ : K₀ ⊆ C₀) (hK₁ : K₁ ⊆ C₁) (hCD : C₀ ∪ C₁ ⊆ D)
    (hgap₀ : ∀ y ∈ domainExitBoundary C₀, y ∉ C₁)
    (hgap₁ : ∀ y ∈ domainExitBoundary C₁, y ∉ C₀)
    (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
      (twoDomainExteriorLabel K₁) x ω = h})
    (us : List PathWord) (hlen : us.length = h.1.length)
    (hu : ∀ p ∈ h.1.zip us, AdmissibleExitWord
      (if p.1.2.1 then C₁ else C₀) p.1.2.2.1 p.1.2.2.2 p.2) :
    pathLaw.real {ω | killedChildRecords D (K₀ ∪ K₁) (C₀ ∪ C₁) x (fun _ w ↦ w) ω = us ∧
      killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁) (twoDomainExteriorLabel K₁) x ω = h} /
      pathLaw.real {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
        (twoDomainExteriorLabel K₁) x ω = h} =
      ((h.1.zip us).map (fun p ↦ (1 / 4 : ℝ) ^ p.2.length /
        traceExitProbability (if p.1.2.1 then C₁ else C₀) p.1.2.2.1 p.1.2.2.2)).prod := by
  rw [exterior_two_domain_bridges hF D K₀ K₁ C₀ C₁ x hK₀ hK₁ hCD hgap₀ hgap₁ h hh us hlen]
  unfold labeledExteriorBridgeWordProduct
  congr 1
  apply List.map_congr_left
  intro p hp
  exact killed_word_bridge_mass hW _ _ _ _ (hu p hp)

end SRWTightness
