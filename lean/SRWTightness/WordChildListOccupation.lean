import SRWTightness.WordChildOccupation

namespace SRWTightness

/-- Different chronological children have different time intervals. -/
theorem wordChildIntervals_nodup (K C : Finset Site) (x : Site) (w : PathWord) :
    (wordChildIntervals K C x w).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.Pairwise.imp_of_mem ?_
    (scanChildIntervals_separated K C x (wordPath w) _ List.pairwise_lt_range none)
  intro a b ha hb hab he
  subst b
  have ht := scanChildIntervals_start_lt_end K C x (wordPath w) _ List.pairwise_lt_range
    none (by intro c hc; cases hc) a ha
  omega

/-- The child list preserves multiplicity even when several child words have identical contents. -/
theorem wordLocalTime_child_list (K C : Finset Site) (hKC : K ⊆ C)
    (x y : Site) (hy : y ∈ K) (w : PathWord)
    (hend : x + position (wordPath w) w.length ∉ C) :
    localTime (wordPath w) w.length (y - x) =
      ((wordChildIntervals K C x w).map (fun q ↦
        localTime (wordPath (slicePathWord w q.1 q.2)) (q.2 - q.1)
          (y - (x + position (wordPath w) q.1)))).sum := by
  rw [wordLocalTime_child_partition K C hKC x y hy w hend]
  rw [← List.sum_toFinset _ (wordChildIntervals_nodup K C x w)]
  apply Finset.sum_congr rfl
  intro q hq
  have ht := wordChildIntervals_endpoint_le K C x w q (List.mem_toFinset.mp hq)
  rw [restricted_visit_sum_eq_Ico (wordPath w) x y q.1 q.2 w.length ht.2,
    interval_visits_eq_shifted_localTime, slicePathWord_localTime]

end SRWTightness
