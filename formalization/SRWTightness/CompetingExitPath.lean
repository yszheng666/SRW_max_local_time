import SRWTightness.ChildExitBounds
import SRWTightness.ExternalKilledExitDecomposition

namespace SRWTightness

/-- A competing exit that leaves the parent is exactly the parent exit time. -/
theorem sdiff_steps_eq_of_exit_outside (D K : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) (hout : domainExitLocation (D \ K) x ω ∉ D) :
    domainSteps (D \ K) x ω = domainSteps D x ω := by
  obtain ⟨_, hle⟩ := subdomain_exit_bounds D (D \ K) Finset.sdiff_subset x ω hfin
  apply Nat.le_antisymm hle
  have he : domainExit D x ω ≤ (domainSteps (D \ K) x ω : WithTop ℕ) :=
    (domainExit_le_iff D x ω _).mpr ⟨_, le_rfl, hout⟩
  rw [← coe_domainSteps D x ω hfin] at he
  exact WithTop.coe_le_coe.mp he

/-- No pre-exit occupation of the inner set makes the competing exit the parent exit. -/
theorem sdiff_steps_eq_of_zero_occupation (D K : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) (hz : setOccupation D K x ω = 0) :
    domainSteps (D \ K) x ω = domainSteps D x ω := by
  obtain ⟨hf, hle⟩ := subdomain_exit_bounds D (D \ K) Finset.sdiff_subset x ω hfin
  apply Nat.le_antisymm hle
  by_contra hn
  have hlt : domainSteps (D \ K) x ω < domainSteps D x ω := Nat.lt_of_not_ge hn
  have hD := position_before_domainSteps_mem D x ω hfin _ hlt
  have hE := position_domain_exit_not_mem (D \ K) x ω hf
  have hK : x + position ω (domainSteps (D \ K) x ω) ∈ K := by
    by_contra hK
    exact hE (Finset.mem_sdiff.mpr ⟨hD, hK⟩)
  have hp := (setOccupation_pos_iff D K x ω).mpr ⟨_, hlt, hK⟩
  omega

/-- A competing exit outside the parent has no earlier inner-set occupation. -/
theorem zero_occupation_of_sdiff_exit_outside (D K : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) (hout : domainExitLocation (D \ K) x ω ∉ D) :
    setOccupation D K x ω = 0 := by
  obtain ⟨hf, _⟩ := subdomain_exit_bounds D (D \ K) Finset.sdiff_subset x ω hfin
  have he := sdiff_steps_eq_of_exit_outside D K x ω hfin hout
  by_contra hz
  have hp : 0 < setOccupation D K x ω := Nat.pos_of_ne_zero hz
  obtain ⟨i, hi, hK⟩ := (setOccupation_pos_iff D K x ω).mp hp
  rw [← he] at hi
  exact (Finset.mem_sdiff.mp (position_before_domainSteps_mem (D \ K) x ω hf i hi)).2 hK

/-- A competing outer-exit atom is escape before inner hitting with the same exit atom. -/
theorem competing_exit_atom_event_iff (D K : Finset Site) (hKD : K ⊆ D)
    (x e : Site) (he : e ∉ D) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    domainExitLocation (D \ K) x ω = e ↔
      domainExit D x ω < setHittingTime K x 0 ω ∧ domainExitLocation D x ω = e := by
  rw [exit_lt_setHittingTime_iff D K hKD x ω hfin]
  constructor
  · intro h
    have hout : domainExitLocation (D \ K) x ω ∉ D := by rwa [h]
    have ht := sdiff_steps_eq_of_exit_outside D K x ω hfin hout
    refine ⟨zero_occupation_of_sdiff_exit_outside D K x ω hfin hout, ?_⟩
    simpa only [domainExitLocation, ht] using h
  · rintro ⟨hz, h⟩
    have ht := sdiff_steps_eq_of_zero_occupation D K x ω hfin hz
    simpa only [domainExitLocation, ht] using h

end SRWTightness
