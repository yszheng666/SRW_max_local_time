import SRWTightness.ExteriorPathRecord
import SRWTightness.NestedWordExtraction

namespace SRWTightness

/-- Standard finite-word boundary-count invariance. Replacing complete internal pieces whose
sites and exit sites lie inside every target preserves the number of recursively extracted
complete outer excursions. This explicit deterministic foundation contains no probability,
source scale, barrier, success event or estimate. -/
def ExteriorNestedCountInvarianceInput : Prop :=
  ∀ (K C : Finset Site) (label : Site → Bool) (x : Site)
    (levels : List (Finset Site × Finset Site)), K ⊆ C →
    (∀ L ∈ levels, L.1 ⊆ L.2 ∧ C ⊆ L.1 ∧ domainExitBoundary C ⊆ (L.1 : Set Site)) →
    ∀ u v : PathWord, wordExteriorRecord K C label x u = wordExteriorRecord K C label x v →
      (terminalWordRecords levels x u).length = (terminalWordRecords levels x v).length

/-- The elementary one-step boundary of a union is contained in the union of the boundaries. -/
theorem domainExitBoundary_union_subset (C₀ C₁ : Finset Site) :
    domainExitBoundary (C₀ ∪ C₁) ⊆ domainExitBoundary C₀ ∪ domainExitBoundary C₁ := by
  rintro y ⟨hy, z, hz, d, hd⟩
  rcases Finset.mem_union.mp hz with hz | hz
  · exact Or.inl ⟨fun h ↦ hy (Finset.mem_union_left _ h), z, hz, d, hd⟩
  · exact Or.inr ⟨fun h ↦ hy (Finset.mem_union_right _ h), z, hz, d, hd⟩

end SRWTightness
