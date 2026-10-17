import SRWTightness.ActualChildRecursion

namespace SRWTightness

/-- A shifted subdomain exit is finite and occurs no later than the original parent exit. -/
theorem shifted_subdomain_exit_bounds (D C : Finset Site) (hCD : C ⊆ D)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤)
    (a : ℕ) (ha : a ≤ domainSteps D x ω) :
    domainExit C (x + position ω a) (shift a ω) ≠ ⊤ ∧
      a + domainSteps C (x + position ω a) (shift a ω) ≤ domainSteps D x ω := by
  have hout : (x + position ω a) + position (shift a ω) (domainSteps D x ω - a) ∉ C := by
    rw [add_assoc, ← position_add, Nat.add_sub_of_le ha]
    exact fun hc ↦ position_domain_exit_not_mem D x ω hfin (hCD hc)
  have hle : domainExit C (x + position ω a) (shift a ω) ≤
      (domainSteps D x ω - a : ℕ) :=
    (domainExit_le_iff C (x + position ω a) (shift a ω) _).mpr ⟨_, le_rfl, hout⟩
  have hf : domainExit C (x + position ω a) (shift a ω) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hle
  refine ⟨hf, ?_⟩
  rw [← coe_domainSteps C (x + position ω a) (shift a ω) hf] at hle
  have hn : domainSteps C (x + position ω a) (shift a ω) ≤ domainSteps D x ω - a :=
    WithTop.coe_le_coe.mp hle
  omega

/-- Exiting any subdomain of a finitely exited parent takes no longer than the parent lifetime. -/
theorem subdomain_exit_bounds (D C : Finset Site) (hCD : C ⊆ D)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    domainExit C x ω ≠ ⊤ ∧ domainSteps C x ω ≤ domainSteps D x ω := by
  have hzero : shift 0 ω = ω := by
    funext k
    simp only [shift, Nat.zero_add]
  have hh := shifted_subdomain_exit_bounds D C hCD x ω hfin 0 (Nat.zero_le _)
  rw [hzero] at hh
  simpa using hh

/-- Nested geometry discharges all child finiteness and lifetime premises of renewal. -/
theorem killedChildIntervals_nested_renewal (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) (x : Site) (ω : Sample) (a b : ℕ)
    (hparent : domainExit D x ω ≠ ⊤)
    (haeq : a = domainSteps (D \ K) x ω)
    (hbeq : b = a + domainSteps C (x + position ω a) (shift a ω))
    (hentry : x + position ω a ∈ K) :
    killedChildIntervals D K C x ω =
      (a, b) :: (killedChildIntervals D K C (x + position ω b) (shift b ω)).map
        (fun q ↦ (b + q.1, b + q.2)) := by
  obtain ⟨hc, hca⟩ := subdomain_exit_bounds D (D \ K) Finset.sdiff_subset x ω hparent
  have ha : a ≤ domainSteps D x ω := by omega
  obtain ⟨hf, hb⟩ := shifted_subdomain_exit_bounds D C hCD x ω hparent a ha
  exact killedChildIntervals_renewal D K C hKC x ω a b hparent haeq hbeq hc hentry hf
    (by omega)

end SRWTightness
