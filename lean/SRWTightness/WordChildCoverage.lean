import SRWTightness.PathWordSlice

namespace SRWTightness

/-- Finite-word coverage depends only on the endpoint leaving the child domain. -/
theorem wordChildIntervals_cover_visit (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (hend : x + position (wordPath w) w.length ∉ C)
    (j : ℕ) (hj : j < w.length) (hvisit : x + position (wordPath w) j ∈ K) :
    ∃ q ∈ wordChildIntervals K C x w, q.1 ≤ j ∧ j < q.2 := by
  apply scanChildIntervals_cover_visit K C hKC x (wordPath w)
    (List.range (w.length + 1)) List.pairwise_lt_range none j
  · simp only [List.mem_range]
    omega
  · exact hvisit
  · intro a h
    cases h
  · exact ⟨w.length, by simp, hj, hend⟩

/-- The one-level extraction remains uniquely covering when applied recursively to a finite word. -/
theorem wordChildIntervals_unique_cover (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (hend : x + position (wordPath w) w.length ∉ C)
    (j : ℕ) (hj : j < w.length) (hvisit : x + position (wordPath w) j ∈ K) :
    ∃! q : ℕ × ℕ, q ∈ wordChildIntervals K C x w ∧ q.1 ≤ j ∧ j < q.2 := by
  obtain ⟨q, hq, hc⟩ := wordChildIntervals_cover_visit K C hKC x w hend j hj hvisit
  refine ⟨q, ⟨hq, hc⟩, ?_⟩
  intro p hp
  exact separated_intervals_cover_unique _
    (scanChildIntervals_separated K C x (wordPath w) _ List.pairwise_lt_range none)
    j p q hp.1 hq hp.2 hc

/-- A finite child ends outside its own child domain, supplying the endpoint for further nesting. -/
theorem wordChildIntervals_slice_endpoint (K C : Finset Site) (x : Site) (w : PathWord)
    (q : ℕ × ℕ) (hq : q ∈ wordChildIntervals K C x w) :
    (x + position (wordPath w) q.1) +
      position (wordPath (slicePathWord w q.1 q.2)) (q.2 - q.1) ∉ C := by
  have hlt := scanChildIntervals_start_lt_end K C x (wordPath w) _
    List.pairwise_lt_range none (by intro a h; cases h) q hq
  have he := (wordChildIntervals_endpoints K C x w q hq).2
  rw [slicePathWord_position w q.1 q.2 _ le_rfl]
  rw [add_assoc, ← position_add, Nat.add_sub_of_le hlt.le]
  exact he

end SRWTightness
