import SRWTightness.ChildActualRenewal
import SRWTightness.DomainStepsShift

namespace SRWTightness

/-- Split the inspected times at a prefix endpoint while retaining the parent exit time. -/
theorem root_time_range_prefix_split (a N : ℕ) (ha : a ≤ N) :
    List.range (N + 1) = List.range a ++ (List.range (N - a + 1)).map (a + ·) := by
  rw [← List.range'_eq_map_range, List.range_eq_range', List.range_eq_range']
  have hh := List.range'_append_1 (s := 0) (m := a) (n := N - a + 1)
  simpa only [Nat.zero_add, show a + (N - a + 1) = N + 1 by omega] using hh.symm

/-- Removing a prefix with no inner entrance preserves every complete child, up to time shift. -/
theorem killedChildIntervals_remove_prefix (D L C : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) (a : ℕ) (ha : a ≤ domainSteps D x ω)
    (hpre : ∀ i < a, x + position ω i ∉ L) :
    killedChildIntervals D L C x ω =
      (killedChildIntervals D L C (x + position ω a) (shift a ω)).map
        (fun q ↦ (a + q.1, a + q.2)) := by
  rw [killedChildIntervals_eq_scan, killedChildIntervals_eq_scan,
    domainSteps_shift_before_exit D x ω hfin a ha, root_time_range_prefix_split a _ ha]
  rw [scanChildIntervals_skip_prefix L C x ω (List.range a) _
    (fun i hi ↦ hpre i (List.mem_range.mp hi))]
  exact scanChildIntervals_shift L C x ω a _ none

/-- In particular, removing a prefix without inner entrances does not change the root count. -/
theorem killedChildIntervals_length_remove_prefix (D L C : Finset Site)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤)
    (a : ℕ) (ha : a ≤ domainSteps D x ω) (hpre : ∀ i < a, x + position ω i ∉ L) :
    (killedChildIntervals D L C x ω).length =
      (killedChildIntervals D L C (x + position ω a) (shift a ω)).length := by
  rw [killedChildIntervals_remove_prefix D L C x ω hfin a ha hpre, List.length_map]

end SRWTightness
