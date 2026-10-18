import SRWTightness.ActualBoundaryEntrances
import SRWTightness.ExteriorRecordSupport

open MeasureTheory
namespace SRWTightness

/-- Actual exterior headers retain the proved boundary support of all complete entrances. -/
theorem killed_exterior_entrance_boundary (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (label : Site → Bool) (x : Site) (hx : x ∉ K) :
    ∀ᵐ ω ∂pathLaw, ∀ s ∈ (killedExteriorRecord D K C label x ω).1,
      s.2.2.1 ∈ domainExitBoundary (D \ K) ∩ (K : Set Site) := by
  filter_upwards [actual_boundary_entrances D K C hKC hCD x hx] with ω hω
  intro s hs
  obtain ⟨q, hq, _, ha, _⟩ := packExteriorRecord_slot label x (killedPathWord D x ω) _ 0 s hs
  have hp : (x + position (wordPath (killedPathWord D x ω)) q.1,
      slicePathWord (killedPathWord D x ω) q.1 q.2) ∈
      killedChildRecords D K C x (fun y u ↦ (y, u)) ω := List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [ha]
  exact hω _ hp

/-- Every slot of a positive exterior atom starts on the actual one-step entrance boundary. -/
theorem exterior_atom_entrance_boundary (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (label : Site → Bool) (x : Site) (hx : x ∉ K) (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D K C label x ω = h}) :
    ∀ s ∈ h.1, s.2.2.1 ∈ domainExitBoundary (D \ K) ∩ (K : Set Site) :=
  support_of_positive_atom pathLaw (killedExteriorRecord D K C label x)
    (fun h ↦ ∀ s ∈ h.1, s.2.2.1 ∈ domainExitBoundary (D \ K) ∩ (K : Set Site))
    (killed_exterior_entrance_boundary D K C hKC hCD label x hx) h hh

end SRWTightness
