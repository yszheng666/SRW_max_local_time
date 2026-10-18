import SRWTightness.ActualEntranceListSupport
import SRWTightness.CompetingBoundarySupport
import SRWTightness.PositiveAtomSupport

open MeasureTheory
namespace SRWTightness

/-- Every actual complete entrance lies on the inner one-step boundary, almost surely. -/
theorem actual_boundary_entrances (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (x : Site) (hx : x ∉ K) :
    ∀ᵐ ω ∂pathLaw, ∀ q ∈ killedChildRecords D K C x (fun y u ↦ (y, u)) ω,
      q.1 ∈ domainExitBoundary (D \ K) ∩ (K : Set Site) := by
  apply ae_support_of_positive_atoms pathLaw (killedChildRecords D K C x (fun y u ↦ (y, u)))
    (fun rs ↦ ∀ q ∈ rs, q.1 ∈ domainExitBoundary (D \ K) ∩ (K : Set Site))
  intro rs hrs
  exact actual_entrance_list_support D K C hKC hCD (K : Set Site)ᶜ
    (domainExitBoundary (D \ K) ∩ (K : Set Site)) (fun _ h ↦ h.2)
    (fun y hy hmem ↦ hy.1 (hKC hmem))
    (fun y hy ↦ competing_boundary_support_of_not_mem D K (hKC.trans hCD) y hy)
    x (competing_boundary_support_of_not_mem D K (hKC.trans hCD) x hx) rs hrs

end SRWTightness
