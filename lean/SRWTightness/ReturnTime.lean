import SRWTightness.SetHitting

open MeasureTheory

namespace SRWTightness

 theorem setHittingTime_isStoppingTime (K : Finset Site) (x : Site) (start : ℕ) :
    IsStoppingTime history (setHittingTime K x start) := by
  have ha : Adapted history (fun n ω ↦ x + position ω n) := by
    intro n
    exact (measurable_of_countable (fun z : Site ↦ x + z)).comp (adapted_position n)
  exact ha.isStoppingTime_hittingAfter (Set.to_countable _).measurableSet

 theorem setHittingTime_le_iff (K : Finset Site) (x : Site) (start n : ℕ) (ω : Sample) :
    setHittingTime K x start ω ≤ n ↔ ∃ k, (start ≤ k ∧ k ≤ n) ∧ x + position ω k ∈ K := by
  simpa [setHittingTime] using (hittingAfter_le_iff
    (u := fun k ω ↦ x + position ω k) (s := (K : Set Site)) (n := start) (i := n) (ω := ω))

 theorem returnTime_succ_le_iff (K : Finset Site) (x : Site) (ω : Sample) (n : ℕ) :
    setHittingTime K x 1 ω ≤ (n + 1 : ℕ) ↔
      setHittingTime K (x + step (ω 0)) 0 (shift 1 ω) ≤ n := by
  rw [setHittingTime_le_iff, setHittingTime_le_iff]
  constructor
  · rintro ⟨k, ⟨hk1, hkn⟩, hmem⟩
    cases k with
    | zero => omega
    | succ k =>
      refine ⟨k, ⟨Nat.zero_le k, by omega⟩, ?_⟩
      simpa only [position_after_first, add_assoc] using hmem
  · rintro ⟨k, ⟨_, hkn⟩, hmem⟩
    refine ⟨k + 1, ⟨by omega, by omega⟩, ?_⟩
    simpa only [position_after_first, add_assoc] using hmem

 theorem returnTime_first_step (K : Finset Site) (x : Site) (ω : Sample) :
    setHittingTime K x 1 ω = 1 + setHittingTime K (x + step (ω 0)) 0 (shift 1 ω) := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro n
  cases n with
  | zero =>
    have hn : ¬ setHittingTime K x 1 ω ≤ (0 : ℕ) := by
      rw [setHittingTime_le_iff]
      rintro ⟨k, ⟨hk1, hk0⟩, _⟩
      omega
    constructor
    · intro h
      exact False.elim (hn h)
    · intro h
      have hh : ¬ (1 : WithTop ℕ) + setHittingTime K (x + step (ω 0)) 0 (shift 1 ω) ≤ 0 := by simp
      exact False.elim (hh h)
  | succ n =>
    apply (returnTime_succ_le_iff K x ω n).trans
    have hcast : ((n + 1 : ℕ) : WithTop ℕ) = (1 : WithTop ℕ) + n := by
      change ((n + 1 : ℕ) : WithTop ℕ) = ((1 + n : ℕ) : WithTop ℕ)
      congr 1
      omega
    change setHittingTime K (x + step (ω 0)) 0 (shift 1 ω) ≤ (n : WithTop ℕ) ↔
      (1 : WithTop ℕ) + setHittingTime K (x + step (ω 0)) 0 (shift 1 ω) ≤ ((n + 1 : ℕ) : WithTop ℕ)
    rw [hcast]
    exact (WithTop.add_le_add_iff_left (by simp : (1 : WithTop ℕ) ≠ ⊤)).symm

 theorem exit_before_return_first_step (D K : Finset Site) (x : Site) (hx : x ∈ D)
    (ω : Sample) :
    domainExit D x ω < setHittingTime K x 1 ω ↔
      domainExit D (x + step (ω 0)) (shift 1 ω) <
        setHittingTime K (x + step (ω 0)) 0 (shift 1 ω) := by
  rw [domainExit_first_step D x hx ω, returnTime_first_step]
  exact WithTop.add_lt_add_iff_left (by simp : (1 : WithTop ℕ) ≠ ⊤)

end SRWTightness
