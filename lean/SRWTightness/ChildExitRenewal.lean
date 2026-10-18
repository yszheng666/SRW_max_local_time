import SRWTightness.ChildActualRenewal

namespace SRWTightness

/-- Including the exit time in the next scan changes nothing when that site is outside K. -/
theorem scanChildIntervals_restart_at_exit (K C : Finset Site) (x : Site) (ω : Sample)
    (b n : ℕ) (hout : x + position ω b ∉ K) :
    (scanChildIntervals K C (x + position ω (b + 1)) (shift (b + 1) ω)
      none (List.range n)).map (fun q ↦ (b + 1 + q.1, b + 1 + q.2)) =
    (scanChildIntervals K C (x + position ω b) (shift b ω)
      none (List.range (n + 1))).map (fun q ↦ (b + q.1, b + q.2)) := by
  rw [← scanChildIntervals_shift K C x ω (b + 1) (List.range n) none,
    ← scanChildIntervals_shift K C x ω b (List.range (n + 1)) none]
  rw [← List.range'_eq_map_range, ← List.range'_eq_map_range, List.range'_succ]
  simp [scanChildIntervals, hout]

/-- The actual first child leaves an exact remaining scan starting at its exit stopping time. -/
theorem killedChildIntervals_restart_at_exit (D K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (a b : ℕ)
    (haeq : a = domainSteps (D \ K) x ω)
    (hbeq : b = a + domainSteps C (x + position ω a) (shift a ω))
    (hfin : domainExit (D \ K) x ω ≠ ⊤)
    (hentry : x + position ω a ∈ K)
    (hchild : domainExit C (x + position ω a) (shift a ω) ≠ ⊤)
    (hb : b ≤ domainSteps D x ω) :
    killedChildIntervals D K C x ω =
      (a, b) :: (scanChildIntervals K C (x + position ω b)
        (shift b ω) none (List.range (domainSteps D x ω - b + 1))).map
          (fun q ↦ (b + q.1, b + q.2)) := by
  rw [killedChildIntervals_actual_restart D K C hKC x ω a b haeq hbeq
    hfin hentry hchild hb]
  congr 1
  apply scanChildIntervals_restart_at_exit
  intro hk
  have he := position_domain_exit_not_mem C (x + position ω a) (shift a ω) hchild
  apply he
  have hc := hKC hk
  simpa only [hbeq, position_add, ← add_assoc] using hc

end SRWTightness
