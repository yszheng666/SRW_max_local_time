import SRWTightness.ExteriorLabelRecordSupport
import SRWTightness.LabeledForestPartition

namespace SRWTightness

/-- The full conditional forests are exactly the chronological forests of their own labeled segments. -/
theorem exterior_forest_partition {M₀ M₁ : Type*}
    (D K₀ K₁ S₀ S₁ C₀ C₁ : Finset Site)
    (hK₀ : K₀ ⊆ S₀) (hK₁ : K₁ ⊆ S₁) (hS₀ : S₀ ⊆ C₀) (hS₁ : S₁ ⊆ C₁)
    (hdisj : Disjoint C₀ C₁) (x : Site) (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
      (twoDomainExteriorLabel K₁) x ω = h})
    (us : List PathWord) (hu : labeledExteriorBridgeWordProduct C₀ C₁ h us ≠ 0)
    (F₀ : Site → PathWord → M₀) (F₁ : Site → PathWord → M₁) :
    let rs₀ := fun p : ExteriorSlot × PathWord ↦ wordChildRecords K₀ S₀ p.1.2.2.1 F₀ p.2
    let rs₁ := fun p : ExteriorSlot × PathWord ↦ wordChildRecords K₁ S₁ p.1.2.2.1 F₁ p.2
    (h.1.zip us).flatMap rs₀ = ((h.1.zip us).filter (fun p ↦ !p.1.2.1)).flatMap rs₀ ∧
    (h.1.zip us).flatMap rs₁ = ((h.1.zip us).filter (fun p ↦ p.1.2.1)).flatMap rs₁ := by
  dsimp only
  have hs := exterior_label_record_support D K₀ K₁ S₀ S₁ C₀ C₁ hK₀ hK₁ hS₀ hS₁
    hdisj x h hh us hu F₀ F₁
  apply two_label_forest_partition (h.1.zip us) (fun p ↦ p.1.2.1)
  · intro p hp hl
    exact ((hs p hp).2 hl).2
  · intro p hp hl
    exact ((hs p hp).1 hl).2

end SRWTightness
