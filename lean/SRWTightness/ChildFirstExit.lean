import SRWTightness.ChildIntervalCompletion
import SRWTightness.SetHitting
import SRWTightness.Shift

namespace SRWTightness

/-- The pending child closes at the first inspected time outside its domain. -/
theorem scanChildIntervals_pending_first_exit (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (ht : ts.Pairwise (· < ·)) (a j : ℕ) (hj : j ∈ ts)
    (hout : x + position ω j ∉ C)
    (hbefore : ∀ i ∈ ts, i < j → x + position ω i ∈ C) :
    ∃ rs, scanChildIntervals K C x ω (some a) ts = (a, j) :: rs := by
  induction ts with
  | nil => simp at hj
  | cons i ts ih =>
    obtain ⟨hi, hts⟩ := List.pairwise_cons.mp ht
    by_cases he : j = i
    · subst j
      refine ⟨scanChildIntervals K C x ω none ts, ?_⟩
      simp [scanChildIntervals, hout]
    · have hjt : j ∈ ts := (List.mem_cons.mp hj).resolve_left he
      have hin : x + position ω i ∈ C := hbefore i List.mem_cons_self (hi j hjt)
      obtain ⟨rs, hrs⟩ := ih hts hjt (fun k hk hkj ↦ hbefore k (List.mem_cons_of_mem i hk) hkj)
      exact ⟨rs, by simpa [scanChildIntervals, hin] using hrs⟩

/-- An entrance followed by its first exit is the first complete emitted child. -/
theorem scanChildIntervals_entry_first_exit (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (ht : ts.Pairwise (· < ·)) (a j : ℕ)
    (ha : x + position ω a ∈ K) (hj : j ∈ ts) (hout : x + position ω j ∉ C)
    (hbefore : ∀ i ∈ ts, i < j → x + position ω i ∈ C) :
    ∃ rs, scanChildIntervals K C x ω none (a :: ts) = (a, j) :: rs := by
  obtain ⟨rs, hrs⟩ := scanChildIntervals_pending_first_exit K C x ω ts ht a j hj hout hbefore
  exact ⟨rs, by simpa [scanChildIntervals, ha] using hrs⟩

/-- Every time strictly before a finite domain exit is still inside the domain. -/
theorem position_before_domainSteps_mem (C : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit C x ω ≠ ⊤) (i : ℕ) (hi : i < domainSteps C x ω) :
    x + position ω i ∈ C := by
  by_contra hout
  have he := (domainExit_le_iff C x ω i).mpr ⟨i, le_rfl, hout⟩
  rw [← coe_domainSteps C x ω hfin] at he
  exact (Nat.not_le_of_lt hi) (WithTop.coe_le_coe.mp he)

/-- The emitted child endpoint is the actual exit of the walk shifted to its entrance. -/
theorem scanChildIntervals_entry_domain_exit (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (ht : ts.Pairwise (· < ·)) (a : ℕ)
    (ha : x + position ω a ∈ K) (hafter : ∀ i ∈ ts, a ≤ i)
    (hfin : domainExit C (x + position ω a) (shift a ω) ≠ ⊤)
    (hj : a + domainSteps C (x + position ω a) (shift a ω) ∈ ts) :
    ∃ rs, scanChildIntervals K C x ω none (a :: ts) =
      (a, a + domainSteps C (x + position ω a) (shift a ω)) :: rs := by
  apply scanChildIntervals_entry_first_exit K C x ω ts ht a _ ha hj
  · simpa only [position_add, ← add_assoc] using
      position_domain_exit_not_mem C (x + position ω a) (shift a ω) hfin
  · intro i hi hij
    have hai := hafter i hi
    have hlt : i - a < domainSteps C (x + position ω a) (shift a ω) := by omega
    have hm := position_before_domainSteps_mem C (x + position ω a) (shift a ω)
      hfin (i - a) hlt
    rw [add_assoc, ← position_add, Nat.add_sub_of_le hai] at hm
    exact hm

end SRWTightness
