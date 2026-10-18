import SRWTightness.ChildVisitUniqueness

namespace SRWTightness

/-- A uniquely covered visit contributes exactly one across all extracted child intervals. -/
theorem killedChildIntervals_indicator_sum (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (j : ℕ)
    (hj : j < domainSteps D x ω) (hvisit : x + position ω j ∈ K) :
    ∑ q ∈ (killedChildIntervals D K C x ω).toFinset,
      (if q.1 ≤ j ∧ j < q.2 then 1 else 0 : ℕ) = 1 := by
  obtain ⟨q, hq, hu⟩ := killedChildIntervals_unique_cover D K C hKC hCD x ω hfin j hj hvisit
  rw [Finset.sum_eq_single q]
  · simp [hq.2]
  · intro p hp hne
    apply if_neg
    intro hc
    exact hne (hu p ⟨List.mem_toFinset.mp hp, hc⟩)
  · intro hn
    exact False.elim (hn (List.mem_toFinset.mpr hq.1))

/-- Restricting each child to the parent visit interval partitions the actual occupation count. -/
theorem domainLocalTime_child_partition (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (x y : Site) (hy : y ∈ K) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    domainLocalTime D x y ω =
      ∑ q ∈ (killedChildIntervals D K C x ω).toFinset,
        ∑ j ∈ Finset.range (domainSteps D x ω),
          (if q.1 ≤ j ∧ j < q.2 then (if x + position ω j = y then 1 else 0) else 0 : ℕ) := by
  rw [Finset.sum_comm]
  unfold domainLocalTime localTime
  apply Finset.sum_congr rfl
  intro j hj
  have he : position ω j = y - x ↔ x + position ω j = y := by
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      calc
        position ω j = (x + position ω j) - x := by abel
        _ = y - x := congrArg (fun z : Site ↦ z - x) h
  by_cases hv : x + position ω j = y
  · rw [if_pos (he.mpr hv)]
    simp only [if_pos hv]
    exact (killedChildIntervals_indicator_sum D K C hKC hCD x ω hfin j
      (Finset.mem_range.mp hj) (hv ▸ hy)).symm
  · rw [if_neg (fun h ↦ hv (he.mp h))]
    simp [hv]

end SRWTightness
