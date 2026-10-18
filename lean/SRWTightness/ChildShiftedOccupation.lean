import SRWTightness.ChildVisitCount
import SRWTightness.Shift
import Mathlib.Algebra.BigOperators.Intervals

namespace SRWTightness

/-- A parent-time restriction equals the count on the child's own half-open time interval. -/
theorem restricted_visit_sum_eq_Ico (ω : Sample) (x y : Site) (a b N : ℕ) (hb : b ≤ N) :
    (∑ j ∈ Finset.range N,
      (if a ≤ j ∧ j < b then (if x + position ω j = y then 1 else 0) else 0 : ℕ)) =
      ∑ j ∈ Finset.Ico a b, (if x + position ω j = y then 1 else 0 : ℕ) := by
  have hs : (Finset.range N).filter (fun j ↦ a ≤ j ∧ j < b) = Finset.Ico a b := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter, hs]

/-- Counting a child interval is counting its shifted SRW path from its actual entrance position. -/
theorem interval_visits_eq_shifted_localTime (ω : Sample) (x y : Site) (a b : ℕ) :
    (∑ j ∈ Finset.Ico a b, (if x + position ω j = y then 1 else 0 : ℕ)) =
      localTime (shift a ω) (b - a) (y - (x + position ω a)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  unfold localTime
  apply Finset.sum_congr rfl
  intro j hj
  rw [position_add]
  have he : x + (position ω a + position (shift a ω) j) = y ↔
      position (shift a ω) j = y - (x + position ω a) := by
    constructor
    · intro h
      calc
        position (shift a ω) j = (x + (position ω a + position (shift a ω) j)) -
          (x + position ω a) := by abel
        _ = y - (x + position ω a) := congrArg (fun z : Site ↦ z - (x + position ω a)) h
    · intro h
      rw [h]
      abel
  simp only [he]

/-- The actual parent's occupation splits into actual shifted child-path occupation counts. -/
theorem domainLocalTime_shifted_children (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (x y : Site) (hy : y ∈ K) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    domainLocalTime D x y ω =
      ∑ q ∈ (killedChildIntervals D K C x ω).toFinset,
        localTime (shift q.1 ω) (q.2 - q.1) (y - (x + position ω q.1)) := by
  rw [domainLocalTime_child_partition D K C hKC hCD x y hy ω hfin]
  apply Finset.sum_congr rfl
  intro q hq
  have ht := wordChildIntervals_endpoint_le K C x (killedPathWord D x ω) q
    (List.mem_toFinset.mp hq)
  rw [restricted_visit_sum_eq_Ico ω x y q.1 q.2 (domainSteps D x ω) ht.2,
    interval_visits_eq_shifted_localTime]

end SRWTightness
