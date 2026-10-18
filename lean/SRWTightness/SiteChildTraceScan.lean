import SRWTightness.SiteListWord
import SRWTightness.RecordExitSlice
import Mathlib.Data.List.Chain

namespace SRWTightness

/-- Read complete child segments from consecutive sites, retaining every site and exit. -/
def scanSiteChildren (K C : Finset Site) :
    Option (Site × List Site) → List Site → List (List Site)
  | _, [] => []
  | none, z :: zs =>
      if z ∈ K then scanSiteChildren K C (some (z, [z])) zs
      else scanSiteChildren K C none zs
  | some (_, acc), z :: zs =>
      if z ∉ C then (acc ++ [z]) :: scanSiteChildren K C none zs
      else scanSiteChildren K C (some (z, acc ++ [z])) zs

/-- A single step from the child domain remains visible in a set containing its exit boundary. -/
theorem child_step_mem_observation (C E : Finset Site) (hCE : C ⊆ E)
    (hboundary : ∀ z ∈ domainExitBoundary C, z ∈ E) (p z : Site)
    (hp : p ∈ C) (hstep : ∃ d : Direction, p + step d = z) : z ∈ E := by
  by_cases hz : z ∈ C
  · exact hCE hz
  · obtain ⟨d, hd⟩ := hstep
    exact hboundary z ⟨hz, p, hp, d, hd.symm⟩

/-- Erasing unobserved sites leaves every complete child's ordered site segment unchanged. -/
theorem scan_site_children_filter (K C E : Finset Site) (hKC : K ⊆ C) (hCE : C ⊆ E)
    (hboundary : ∀ z ∈ domainExitBoundary C, z ∈ E) (zs : List Site)
    (s : Option (Site × List Site))
    (hchain : List.IsChain (fun p z ↦ ∃ d : Direction, p + step d = z) zs)
    (hactive : ∀ p acc, s = some (p, acc) → p ∈ C ∧
      ∀ z ∈ zs.head?, ∃ d : Direction, p + step d = z) :
    scanSiteChildren K C s (zs.filter (fun z ↦ z ∈ E)) = scanSiteChildren K C s zs := by
  induction zs generalizing s with
  | nil => rfl
  | cons z zs ih =>
    have hc := List.isChain_cons.mp hchain
    have hnone : ∀ p acc, (none : Option (Site × List Site)) = some (p, acc) →
        p ∈ C ∧ ∀ y ∈ zs.head?, ∃ d : Direction, p + step d = y := by
      intro p acc he
      cases he
    have hnext (acc : List Site) (hz : z ∈ C) :
        ∀ p as, some (z, acc) = some (p, as) →
          p ∈ C ∧ ∀ y ∈ zs.head?, ∃ d : Direction, p + step d = y := by
      intro p as he
      cases he
      exact ⟨hz, hc.1⟩
    cases s with
    | none =>
      by_cases hz : z ∈ K
      · have hzE := hCE (hKC hz)
        simpa [scanSiteChildren, hz, hzE] using
          ih (some (z, [z])) hc.2 (hnext [z] (hKC hz))
      · by_cases hzE : z ∈ E <;>
          simpa [scanSiteChildren, hz, hzE] using ih none hc.2 hnone
    | some q =>
      rcases q with ⟨p, acc⟩
      have ha := hactive p acc rfl
      have hzE := child_step_mem_observation C E hCE hboundary p z ha.1
        (ha.2 z (by simp))
      by_cases hz : z ∈ C
      · simpa [scanSiteChildren, hz, hzE] using
          ih (some (z, acc ++ [z])) hc.2 (hnext (acc ++ [z]) hz)
      · simpa [scanSiteChildren, hz, hzE] using
          congrArg (List.cons (acc ++ [z])) (ih none hc.2 hnone)

end SRWTightness
