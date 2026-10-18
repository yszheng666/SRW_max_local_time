import SRWTightness.ChildScanBoundaryReset
import SRWTightness.ChildActualRenewal
import SRWTightness.DomainStepsShift

namespace SRWTightness

/-- Split inspected times after an included boundary point, also when it is the final point. -/
theorem child_time_boundary_split (n N : ℕ) (hn : n ≤ N) :
    List.range (N + 1) = (List.range n ++ [n]) ++ List.range' (n + 1) (N - n) := by
  have he : n + 1 + (N - n) = N + 1 := by omega
  have hh := (List.range'_append_1 (s := 0) (m := n + 1) (n := N - n)).symm
  simpa only [Nat.zero_add, he, ← List.range_eq_range', List.range_succ] using hh

/-- An outside-domain cut preserves every earlier child and restarts an empty shifted scan. -/
theorem scan_child_intervals_boundary_split (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (n N : ℕ) (hn : n ≤ N) (hout : x + position ω n ∉ C) :
    scanChildIntervals K C x ω none (List.range (N + 1)) =
      scanChildIntervals K C x ω none (List.range (n + 1)) ++
        (scanChildIntervals K C (x + position ω n) (shift n ω) none
          (List.range (N - n + 1))).map (fun q ↦ (n + q.1, n + q.2)) := by
  have hnotK : x + position ω n ∉ K := fun h ↦ hout (hKC h)
  have hskip : scanChildIntervals K C x ω none (List.range' (n + 1) (N - n)) =
      scanChildIntervals K C x ω none (List.range' n (N - n + 1)) := by
    rw [List.range'_succ]
    simp only [scanChildIntervals, if_neg hnotK]
  calc
    _ = scanChildIntervals K C x ω none
        ((List.range n ++ [n]) ++ List.range' (n + 1) (N - n)) := by
      rw [child_time_boundary_split n N hn]
    _ = scanChildIntervals K C x ω none (List.range n ++ [n]) ++
        scanChildIntervals K C x ω none (List.range' (n + 1) (N - n)) :=
      scanChildIntervals_append_outside K C hKC x ω _ _ n hout none
    _ = scanChildIntervals K C x ω none (List.range (n + 1)) ++
        scanChildIntervals K C x ω none (List.range' (n + 1) (N - n)) := by
      rw [← List.range_succ]
    _ = _ := by
      congr 1
      rw [hskip, List.range'_eq_map_range]
      exact scanChildIntervals_shift K C x ω n (List.range (N - n + 1)) none

/-- The boundary cut decomposes the complete-child count into prefix and restarted suffix counts. -/
theorem scan_child_count_boundary_split (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (n N : ℕ) (hn : n ≤ N) (hout : x + position ω n ∉ C) :
    (scanChildIntervals K C x ω none (List.range (N + 1))).length =
      (scanChildIntervals K C x ω none (List.range (n + 1))).length +
        (scanChildIntervals K C (x + position ω n) (shift n ω) none
          (List.range (N - n + 1))).length := by
  rw [scan_child_intervals_boundary_split K C hKC x ω n N hn hout,
    List.length_append, List.length_map]

/-- The actual killed count decomposes at every inspected point outside its child domain. -/
theorem killed_child_count_boundary_split (D K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (n : ℕ)
    (hn : n ≤ domainSteps D x ω) (hout : x + position ω n ∉ C) :
    (killedChildIntervals D K C x ω).length =
      (scanChildIntervals K C x ω none (List.range (n + 1))).length +
        (killedChildIntervals D K C (x + position ω n) (shift n ω)).length := by
  rw [killedChildIntervals_eq_scan, killedChildIntervals_eq_scan,
    domainSteps_shift_before_exit D x ω hfin n hn]
  exact scan_child_count_boundary_split K C hKC x ω n _ hn hout

end SRWTightness
