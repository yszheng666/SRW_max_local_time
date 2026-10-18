import SRWTightness.WordComponentSupport
import SRWTightness.KilledWordBridgeSupport
import SRWTightness.ExternalExteriorBridge
import Mathlib.Algebra.BigOperators.Ring.List

namespace SRWTightness

/-- Nonzero labeled bridge products contain only admissible component words. -/
theorem labeled_exterior_bridge_support (C₀ C₁ : Finset Site) (h : ExteriorPathRecord)
    (us : List PathWord) (hu : labeledExteriorBridgeWordProduct C₀ C₁ h us ≠ 0) :
    ∀ p ∈ h.1.zip us, AdmissibleExitWord (if p.1.2.1 then C₁ else C₀)
      p.1.2.2.1 p.1.2.2.2 p.2 := by
  intro p hp
  apply killed_word_bridge_admissible
  intro hz
  apply hu
  exact List.prod_eq_zero (List.mem_map.mpr ⟨p, hp, hz⟩)

/-- Each supported exterior slot has nonempty roots at its recorded label and none at the other site. -/
theorem exterior_label_record_support {M₀ M₁ : Type*}
    (D K₀ K₁ S₀ S₁ C₀ C₁ : Finset Site)
    (hK₀ : K₀ ⊆ S₀) (hK₁ : K₁ ⊆ S₁) (hS₀ : S₀ ⊆ C₀) (hS₁ : S₁ ⊆ C₁)
    (hdisj : Disjoint C₀ C₁) (x : Site) (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
      (twoDomainExteriorLabel K₁) x ω = h})
    (us : List PathWord) (hu : labeledExteriorBridgeWordProduct C₀ C₁ h us ≠ 0)
    (F₀ : Site → PathWord → M₀) (F₁ : Site → PathWord → M₁) :
    ∀ p ∈ h.1.zip us,
      (p.1.2.1 = false →
        wordChildRecords K₀ S₀ p.1.2.2.1 F₀ p.2 ≠ [] ∧
        wordChildRecords K₁ S₁ p.1.2.2.1 F₁ p.2 = []) ∧
      (p.1.2.1 = true →
        wordChildRecords K₁ S₁ p.1.2.2.1 F₁ p.2 ≠ [] ∧
        wordChildRecords K₀ S₀ p.1.2.2.1 F₀ p.2 = []) := by
  intro p hp
  have hs := exterior_atom_slot D (K₀ ∪ K₁) (C₀ ∪ C₁)
    (twoDomainExteriorLabel K₁) x h hh p.1 (List.of_mem_zip hp).1
  have hw := labeled_exterior_bridge_support C₀ C₁ h us hu p hp
  constructor
  · intro hl
    have hn : p.1.2.2.1 ∉ K₁ := by
      have hh := hs.2.2
      rw [hl] at hh
      simpa only [twoDomainExteriorLabel, decide_eq_false_iff_not] using hh.symm
    have hx := (Finset.mem_union.mp hs.1).resolve_right hn
    simp only [hl, Bool.false_eq_true, if_false] at hw
    exact ⟨admissible_word_own_records_nonempty K₀ S₀ C₀ hK₀ hS₀ _ _ _ hx hw F₀,
      admissible_word_opposite_records_empty C₀ C₁ K₁ S₁ hdisj (hK₁.trans hS₁) _ _ _ hw F₁⟩
  · intro hl
    have hx : p.1.2.2.1 ∈ K₁ := by
      have hh := hs.2.2
      rw [hl] at hh
      simpa only [twoDomainExteriorLabel, decide_eq_true_eq] using hh.symm
    simp only [hl, if_true] at hw
    exact ⟨admissible_word_own_records_nonempty K₁ S₁ C₁ hK₁ hS₁ _ _ _ hx hw F₁,
      admissible_word_opposite_records_empty C₁ C₀ K₀ S₀ hdisj.symm (hK₀.trans hS₀) _ _ _ hw F₀⟩

end SRWTightness
