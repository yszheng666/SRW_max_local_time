import SRWTightness.ChildRangeRenewal

namespace SRWTightness

/-- Full-range renewal at the actual competing entrance and actual child exit. -/
theorem scanChildIntervals_actual_range_restart (D K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (a b N : ℕ)
    (haeq : a = domainSteps (D \ K) x ω)
    (hbeq : b = a + domainSteps C (x + position ω a) (shift a ω))
    (hfin : domainExit (D \ K) x ω ≠ ⊤)
    (hentry : x + position ω a ∈ K)
    (hchild : domainExit C (x + position ω a) (shift a ω) ≠ ⊤) (hb : b ≤ N) :
    scanChildIntervals K C x ω none (List.range (N + 1)) =
      (a, b) :: (scanChildIntervals K C (x + position ω (b + 1))
        (shift (b + 1) ω) none (List.range (N - b))).map
          (fun q ↦ (b + 1 + q.1, b + 1 + q.2)) := by
  have he := position_domain_exit_not_mem C (x + position ω a) (shift a ω) hchild
  have hpos : 0 < domainSteps C (x + position ω a) (shift a ω) := by
    by_contra hn
    have hz : domainSteps C (x + position ω a) (shift a ω) = 0 := by omega
    rw [hz] at he
    exact he (by simpa using hKC hentry)
  have hab : a < b := by omega
  apply scanChildIntervals_range_restart K C x ω a b N hab hb
  · intro i hi
    exact (Finset.mem_sdiff.mp (position_before_domainSteps_mem (D \ K) x ω hfin i
      (by omega))).2
  · exact hentry
  · intro i hai hib
    have hlt : i - a < domainSteps C (x + position ω a) (shift a ω) := by omega
    have hm := position_before_domainSteps_mem C (x + position ω a) (shift a ω)
      hchild (i - a) hlt
    rw [add_assoc, ← position_add, Nat.add_sub_of_le hai.le] at hm
    exact hm
  · simpa only [hbeq, position_add, ← add_assoc] using he

/-- Scanning depends only on the positions at the inspected times. -/
theorem scanChildIntervals_position_congr (K C : Finset Site) (x : Site) (ω υ : Sample)
    (ts : List ℕ) (s : Option ℕ) (hpos : ∀ i ∈ ts, position ω i = position υ i) :
    scanChildIntervals K C x ω s ts = scanChildIntervals K C x υ s ts := by
  induction ts generalizing s with
  | nil => rfl
  | cons i ts ih =>
    have hi := hpos i List.mem_cons_self
    have ht := fun j hj ↦ hpos j (List.mem_cons_of_mem i hj)
    cases s with
    | none =>
      simp only [scanChildIntervals, hi]
      split_ifs <;> exact ih _ ht
    | some a =>
      simp only [scanChildIntervals, hi]
      split_ifs
      · exact ih (some a) ht
      · exact congrArg (List.cons (a, i)) (ih none ht)

/-- The recorded killed-word extractor is exactly the full actual-path scan. -/
theorem killedChildIntervals_eq_scan (D K C : Finset Site) (x : Site) (ω : Sample) :
    killedChildIntervals D K C x ω =
      scanChildIntervals K C x ω none (List.range (domainSteps D x ω + 1)) := by
  apply scanChildIntervals_position_congr
  intro i hi
  exact killedPathWord_position D x ω i (by simpa [killedPathWord] using List.mem_range.mp hi)

/-- Actual killed-path child extraction has the same explicit remainder after its first child. -/
theorem killedChildIntervals_actual_restart (D K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (a b : ℕ)
    (haeq : a = domainSteps (D \ K) x ω)
    (hbeq : b = a + domainSteps C (x + position ω a) (shift a ω))
    (hfin : domainExit (D \ K) x ω ≠ ⊤)
    (hentry : x + position ω a ∈ K)
    (hchild : domainExit C (x + position ω a) (shift a ω) ≠ ⊤)
    (hb : b ≤ domainSteps D x ω) :
    killedChildIntervals D K C x ω =
      (a, b) :: (scanChildIntervals K C (x + position ω (b + 1))
        (shift (b + 1) ω) none (List.range (domainSteps D x ω - b))).map
          (fun q ↦ (b + 1 + q.1, b + 1 + q.2)) := by
  rw [killedChildIntervals_eq_scan]
  exact scanChildIntervals_actual_range_restart D K C hKC x ω a b _
    haeq hbeq hfin hentry hchild hb

end SRWTightness
