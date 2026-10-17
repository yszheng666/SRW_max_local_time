import SRWTightness.ExternalExteriorBridge

namespace SRWTightness

/-- Actual exterior fibers for separated domains factor into the bridges selected by their labels. -/
theorem exterior_two_domain_bridges (hF : ExteriorBridgeFactorizationInput)
    (D K₀ K₁ C₀ C₁ : Finset Site) (x : Site)
    (hK₀ : K₀ ⊆ C₀) (hK₁ : K₁ ⊆ C₁) (hCD : C₀ ∪ C₁ ⊆ D)
    (hgap₀ : ∀ y ∈ domainExitBoundary C₀, y ∉ C₁)
    (hgap₁ : ∀ y ∈ domainExitBoundary C₁, y ∉ C₀)
    (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
      (twoDomainExteriorLabel K₁) x ω = h})
    (us : List PathWord) (hlen : us.length = h.1.length) :
    pathLaw.real {ω | killedChildRecords D (K₀ ∪ K₁) (C₀ ∪ C₁) x (fun _ w ↦ w) ω = us ∧
      killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁) (twoDomainExteriorLabel K₁) x ω = h} /
      pathLaw.real {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
        (twoDomainExteriorLabel K₁) x ω = h} = labeledExteriorBridgeWordProduct C₀ C₁ h us := by
  rw [hF D (K₀ ∪ K₁) (C₀ ∪ C₁) (twoDomainExteriorLabel K₁) x
    (Finset.union_subset_union hK₀ hK₁) hCD h hh us hlen]
  unfold exteriorBridgeWordProduct labeledExteriorBridgeWordProduct
  congr 1
  apply List.map_congr_left
  intro p hp
  have hslot := exterior_atom_slot D (K₀ ∪ K₁) (C₀ ∪ C₁)
    (twoDomainExteriorLabel K₁) x h hh p.1 (List.of_mem_zip hp).1
  by_cases hy : p.1.2.2.1 ∈ K₁
  · have hl : p.1.2.1 = true := by rw [hslot.2.2]; simp [twoDomainExteriorLabel, hy]
    simp only [hl, Bool.true_eq, ite_true]
    rw [Finset.union_comm]
    exact separated_union_word_bridge C₁ C₀ _ _ (hK₁ hy) hgap₁ p.2
  · have hstart : p.1.2.2.1 ∈ K₀ := (Finset.mem_union.mp hslot.1).resolve_right hy
    have hl : p.1.2.1 = false := by rw [hslot.2.2]; simp [twoDomainExteriorLabel, hy]
    simp only [hl, Bool.false_eq_true, ite_false]
    exact separated_union_word_bridge C₀ C₁ _ _ (hK₀ hstart) hgap₀ p.2

end SRWTightness
