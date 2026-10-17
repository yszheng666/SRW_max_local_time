import SRWTightness.ChildExitBounds
import SRWTightness.KilledPathWord

namespace SRWTightness

/-- Agreement through a finite exit preserves both exit finiteness and the exact lifetime. -/
theorem domainSteps_eq_of_positions (D : Finset Site) (x : Site) (ω υ : Sample)
    (hfin : domainExit D x ω ≠ ⊤)
    (hp : ∀ i ≤ domainSteps D x ω, position ω i = position υ i) :
    domainExit D x υ ≠ ⊤ ∧ domainSteps D x ω = domainSteps D x υ := by
  have hout : x + position υ (domainSteps D x ω) ∉ D := by
    rw [← hp _ le_rfl]
    exact position_domain_exit_not_mem D x ω hfin
  have he : domainExit D x υ ≤ (domainSteps D x ω : WithTop ℕ) :=
    (domainExit_le_iff D x υ _).mpr ⟨_, le_rfl, hout⟩
  have hv : domainExit D x υ ≠ ⊤ := ne_top_of_le_ne_top (by simp) he
  have hle : domainSteps D x υ ≤ domainSteps D x ω := by
    rw [← coe_domainSteps D x υ hv] at he
    exact WithTop.coe_le_coe.mp he
  refine ⟨hv, Nat.le_antisymm ?_ hle⟩
  by_contra hn
  have ht : domainSteps D x υ < domainSteps D x ω := by omega
  have hm := position_before_domainSteps_mem D x ω hfin _ ht
  rw [hp _ hle] at hm
  exact position_domain_exit_not_mem D x υ hv hm

/-- The complete killed word depends only on the increments before its finite parent exit. -/
theorem killedPathWord_eq_of_prefix (D : Finset Site) (x : Site) (ω υ : Sample)
    (hfin : domainExit D x ω ≠ ⊤)
    (hω : ∀ i < domainSteps D x ω, ω i = υ i) :
    killedPathWord D x ω = killedPathWord D x υ := by
  have hp (i : ℕ) (hi : i ≤ domainSteps D x ω) : position ω i = position υ i := by
    apply position_congr
    intro k hk
    exact hω k (hk.trans_le hi)
  have he := (domainSteps_eq_of_positions D x ω υ hfin hp).2
  simp only [killedPathWord]
  congr 1
  apply (Fin.heq_fun_iff he).mpr
  intro k
  exact hω k k.isLt

end SRWTightness
