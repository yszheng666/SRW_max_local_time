import SRWTightness.WordChildCoverage

namespace SRWTightness

/-- A uniquely covered visit contributes exactly one across all extracted child intervals. -/
theorem wordChildIntervals_indicator_sum (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (hend : x + position (wordPath w) w.length ∉ C) (j : ℕ)
    (hj : j < w.length) (hvisit : x + position (wordPath w) j ∈ K) :
    ∑ q ∈ (wordChildIntervals K C x w).toFinset,
      (if q.1 ≤ j ∧ j < q.2 then 1 else 0 : ℕ) = 1 := by
  obtain ⟨q, hq, hu⟩ := wordChildIntervals_unique_cover K C hKC x w hend j hj hvisit
  rw [Finset.sum_eq_single q]
  · simp [hq.2]
  · intro p hp hne
    apply if_neg
    intro hc
    exact hne (hu p ⟨List.mem_toFinset.mp hp, hc⟩)
  · intro hn
    exact False.elim (hn (List.mem_toFinset.mpr hq.1))

/-- Restricting each child to the parent visit interval partitions the finite-word occupation count. -/
theorem wordLocalTime_child_partition (K C : Finset Site) (hKC : K ⊆ C)
    (x y : Site) (hy : y ∈ K) (w : PathWord) (hend : x + position (wordPath w) w.length ∉ C) :
    localTime (wordPath w) w.length (y - x) =
      ∑ q ∈ (wordChildIntervals K C x w).toFinset,
        ∑ j ∈ Finset.range (w.length),
          (if q.1 ≤ j ∧ j < q.2 then (if x + position (wordPath w) j = y then 1 else 0) else 0 : ℕ) := by
  rw [Finset.sum_comm]
  unfold localTime
  apply Finset.sum_congr rfl
  intro j hj
  have he : position (wordPath w) j = y - x ↔ x + position (wordPath w) j = y := by
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      calc
        position (wordPath w) j = (x + position (wordPath w) j) - x := by abel
        _ = y - x := congrArg (fun z : Site ↦ z - x) h
  by_cases hv : x + position (wordPath w) j = y
  · rw [if_pos (he.mpr hv)]
    simp only [if_pos hv]
    exact (wordChildIntervals_indicator_sum K C hKC x w hend j
      (Finset.mem_range.mp hj) (hv ▸ hy)).symm
  · rw [if_neg (fun h ↦ hv (he.mp h))]
    simp [hv]

end SRWTightness
