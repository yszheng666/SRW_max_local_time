import SRWTightness.ChildExitBounds
import SRWTightness.RecordExitSlice
import SRWTightness.KilledPathWord

open MeasureTheory
namespace SRWTightness

/-- If the other domain avoids the one-step exit boundary, adjoining it does not change the exit time. -/
theorem separated_union_domainSteps_ae (C E : Finset Site) (x : Site) (hx : x ∈ C)
    (hgap : ∀ y ∈ domainExitBoundary C, y ∉ E) :
    ∀ᵐ ω ∂pathLaw, domainSteps (C ∪ E) x ω = domainSteps C x ω := by
  filter_upwards [domainExit_ne_top_ae (C ∪ E) x,
    domainExitLocation_mem_boundary_ae C x hx] with ω hfin hb
  obtain ⟨hCfin, hle⟩ := subdomain_exit_bounds (C ∪ E) C Finset.subset_union_left x ω hfin
  have hout : x + position ω (domainSteps C x ω) ∉ C ∪ E := by
    change domainExitLocation C x ω ∉ C ∪ E
    intro hy
    rcases Finset.mem_union.mp hy with hc | he
    · exact hb.1 hc
    · exact hgap _ hb he
  have hother := (domainExit_le_iff (C ∪ E) x ω (domainSteps C x ω)).mpr
    ⟨_, le_rfl, hout⟩
  rw [← coe_domainSteps (C ∪ E) x ω hfin] at hother
  exact le_antisymm (WithTop.coe_le_coe.mp hother) hle

/-- The entire deleted internal word is unchanged when a separated domain is adjoined. -/
theorem separated_union_killedPathWord_ae (C E : Finset Site) (x : Site) (hx : x ∈ C)
    (hgap : ∀ y ∈ domainExitBoundary C, y ∉ E) :
    ∀ᵐ ω ∂pathLaw, killedPathWord (C ∪ E) x ω = killedPathWord C x ω := by
  filter_upwards [separated_union_domainSteps_ae C E x hx hgap] with ω hω
  exact congrArg (fun n : ℕ ↦ (⟨n, fun k ↦ ω k⟩ : PathWord)) hω

end SRWTightness
