import SRWTightness.ExteriorPositiveWordAtom
import SRWTightness.ExteriorTwoDomainBridges
import Mathlib.Algebra.BigOperators.Ring.List

open MeasureTheory
namespace SRWTightness

/-- A nonzero bridge word can only prescribe an exit with positive probability. -/
theorem killed_word_bridge_exit_positive (C : Finset Site) (x e : Site) (w : PathWord)
    (hw : killedWordBridgeProbability C x e w ≠ 0) : 0 < traceExitProbability C x e := by
  apply lt_of_le_of_ne measureReal_nonneg
  intro hz
  apply hw
  change 0 = traceExitProbability C x e at hz
  rw [killedWordBridgeProbability, ← hz, div_zero]

/-- Every slot of a supported labeled bridge product has a reachable prescribed exit. -/
theorem labeled_exterior_bridge_exit_positive (C₀ C₁ : Finset Site)
    (h : ExteriorPathRecord) (us : List PathWord)
    (hlen : us.length = h.1.length)
    (hu : labeledExteriorBridgeWordProduct C₀ C₁ h us ≠ 0) :
    ∀ s ∈ h.1, 0 < traceExitProbability (if s.2.1 then C₁ else C₀) s.2.2.1 s.2.2.2 := by
  intro s hs
  have hm : s ∈ (h.1.zip us).map Prod.fst := by
    rw [List.map_fst_zip (by omega)]
    exact hs
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  apply killed_word_bridge_exit_positive _ _ _ p.2
  intro hz
  apply hu
  exact List.prod_eq_zero (List.mem_map.mpr ⟨p, hp, hz⟩)

/-- Positive actual exterior atoms have reachable exits in the component selected by every label. -/
theorem exterior_atom_exit_positive (hF : ExteriorBridgeFactorizationInput)
    (D K₀ K₁ C₀ C₁ : Finset Site) (x : Site)
    (hK₀ : K₀ ⊆ C₀) (hK₁ : K₁ ⊆ C₁) (hCD : C₀ ∪ C₁ ⊆ D)
    (hgap₀ : ∀ y ∈ domainExitBoundary C₀, y ∉ C₁)
    (hgap₁ : ∀ y ∈ domainExitBoundary C₁, y ∉ C₀)
    (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
      (twoDomainExteriorLabel K₁) x ω = h}) :
    ∀ s ∈ h.1, 0 < traceExitProbability (if s.2.1 then C₁ else C₀) s.2.2.1 s.2.2.2 := by
  obtain ⟨us, hlen, hpos⟩ := exterior_positive_word_atom D (K₀ ∪ K₁) (C₀ ∪ C₁)
    (twoDomainExteriorLabel K₁) x h hh
  have he := exterior_two_domain_bridges hF D K₀ K₁ C₀ C₁ x hK₀ hK₁ hCD
    hgap₀ hgap₁ h hh us hlen
  have hu : labeledExteriorBridgeWordProduct C₀ C₁ h us ≠ 0 := by
    rw [← he]
    exact (div_pos hpos hh).ne'
  exact labeled_exterior_bridge_exit_positive C₀ C₁ h us hlen hu

end SRWTightness
