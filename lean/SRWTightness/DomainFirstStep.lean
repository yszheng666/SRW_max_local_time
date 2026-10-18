import SRWTightness.FiniteDomain
import SRWTightness.Shift

namespace SRWTightness

@[simp] theorem position_zero_as_zero (ω : Sample) : position ω 0 = (0 : Site) := rfl

@[simp] theorem position_one_as_step (ω : Sample) : position ω 1 = step (ω 0) := by
  change (0 : Site) + step (ω 0) = step (ω 0)
  exact zero_add _

 theorem position_after_first (ω : Sample) (n : ℕ) :
    position ω (n + 1) = step (ω 0) + position (shift 1 ω) n := by
  have h := position_add ω 1 n
  simpa only [Nat.add_comm 1 n, position_one_as_step] using h

 theorem domainExit_eq_zero_of_not_mem (D : Finset Site) (x : Site) (hx : x ∉ D) (ω : Sample) :
    domainExit D x ω = 0 := by
  apply le_antisymm _ bot_le
  apply (domainExit_le_iff D x ω 0).mpr
  exact ⟨0, le_rfl, by simpa only [position_zero_as_zero, add_zero] using hx⟩

 theorem domainExit_succ_le_iff (D : Finset Site) (x : Site) (hx : x ∈ D)
    (ω : Sample) (n : ℕ) :
    domainExit D x ω ≤ (n + 1 : ℕ) ↔
      domainExit D (x + step (ω 0)) (shift 1 ω) ≤ n := by
  rw [domainExit_le_iff, domainExit_le_iff]
  constructor
  · rintro ⟨k, hk, hout⟩
    cases k with
    | zero => exact False.elim (hout (by simpa only [position_zero_as_zero, add_zero] using hx))
    | succ k =>
      refine ⟨k, by omega, ?_⟩
      simpa only [position_after_first, add_assoc] using hout
  · rintro ⟨k, hk, hout⟩
    refine ⟨k + 1, by omega, ?_⟩
    simpa only [position_after_first, add_assoc] using hout

 theorem domainExit_first_step (D : Finset Site) (x : Site) (hx : x ∈ D) (ω : Sample) :
    domainExit D x ω = 1 + domainExit D (x + step (ω 0)) (shift 1 ω) := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro n
  cases n with
  | zero =>
    have hn : ¬ domainExit D x ω ≤ (0 : ℕ) := by
      rw [domainExit_le_iff]
      rintro ⟨k, hk, hout⟩
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact hout (by simpa only [position_zero_as_zero, add_zero] using hx)
    constructor
    · intro h
      exact False.elim (hn h)
    · intro h
      have hh : ¬ (1 : WithTop ℕ) + domainExit D (x + step (ω 0)) (shift 1 ω) ≤ 0 := by simp
      exact False.elim (hh h)
  | succ n =>
    apply (domainExit_succ_le_iff D x hx ω n).trans
    have hcast : ((n + 1 : ℕ) : WithTop ℕ) = (1 : WithTop ℕ) + n := by
      change ((n + 1 : ℕ) : WithTop ℕ) = ((1 + n : ℕ) : WithTop ℕ)
      congr 1
      omega
    constructor
    · intro h
      have hh : (1 : WithTop ℕ) + domainExit D (x + step (ω 0)) (shift 1 ω) ≤ 1 + (n : WithTop ℕ) :=
        add_le_add (le_refl (1 : WithTop ℕ)) h
      exact hh.trans_eq hcast.symm
    · intro h
      have hh : (1 : WithTop ℕ) + domainExit D (x + step (ω 0)) (shift 1 ω) ≤ 1 + (n : WithTop ℕ) :=
        h.trans_eq hcast
      exact (WithTop.add_le_add_iff_left (by simp : (1 : WithTop ℕ) ≠ ⊤)).mp hh


end SRWTightness
