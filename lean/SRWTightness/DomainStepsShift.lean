import SRWTightness.ChildFirstExit

namespace SRWTightness

/-- Before parent exit, shifting the actual walk subtracts the elapsed time from its lifetime. -/
theorem domainSteps_shift_before_exit (D : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) (b : ℕ) (hb : b ≤ domainSteps D x ω) :
    domainSteps D (x + position ω b) (shift b ω) = domainSteps D x ω - b := by
  have hout : (x + position ω b) + position (shift b ω) (domainSteps D x ω - b) ∉ D := by
    rw [add_assoc, ← position_add, Nat.add_sub_of_le hb]
    exact position_domain_exit_not_mem D x ω hfin
  have hle : domainExit D (x + position ω b) (shift b ω) ≤
      (domainSteps D x ω - b : ℕ) :=
    (domainExit_le_iff D (x + position ω b) (shift b ω) _).mpr ⟨_, le_rfl, hout⟩
  have hf : domainExit D (x + position ω b) (shift b ω) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hle
  have hn : domainSteps D (x + position ω b) (shift b ω) ≤ domainSteps D x ω - b := by
    rw [← coe_domainSteps D (x + position ω b) (shift b ω) hf] at hle
    exact WithTop.coe_le_coe.mp hle
  apply Nat.le_antisymm hn
  by_contra hg
  have hi : b + domainSteps D (x + position ω b) (shift b ω) < domainSteps D x ω := by
    omega
  have hm := position_before_domainSteps_mem D x ω hfin _ hi
  rw [position_add, ← add_assoc] at hm
  exact position_domain_exit_not_mem D (x + position ω b) (shift b ω) hf hm

end SRWTightness
