import SRWTightness.ChildCompletionPrefix

namespace SRWTightness

/-- Completions strictly after an outside cut are exactly the restarted suffix completions. -/
theorem scan_child_completion_after_cut_length (L C : Finset Site) (hLC : L ⊆ C)
    (x : Site) (ω : Sample) (n N : ℕ) (hn : n ≤ N) (hout : x + position ω n ∉ C) :
    ((scanChildCompletionTimes L C x ω N).filter (fun k ↦ n < k)).length =
      (scanChildIntervals L C (x + position ω n) (shift n ω) none
        (List.range (N - n + 1))).length := by
  let pre := scanChildCompletionTimes L C x ω n
  let tail := scanChildIntervals L C (x + position ω n) (shift n ω) none
    (List.range (N - n + 1))
  have hpre : pre.filter (fun k ↦ n < k) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro k hk
    have hle := scan_child_completion_time_le L C x ω n k hk
    simp [not_lt_of_ge hle]
  have htail : (tail.map (fun q ↦ n + q.2)).filter (fun k ↦ n < k) =
      tail.map (fun q ↦ n + q.2) := by
    apply List.filter_eq_self.mpr
    intro k hk
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hk
    have hlt := scanChildIntervals_start_lt_end L C (x + position ω n) (shift n ω) _
      List.pairwise_lt_range none (by intro a h; cases h) q hq
    simp [show n < n + q.2 by omega]
  have hs : scanChildCompletionTimes L C x ω N = pre ++
      tail.map (fun q ↦ n + q.2) := by
    unfold scanChildCompletionTimes
    rw [scan_child_intervals_boundary_split L C hLC x ω n N hn hout,
      List.map_append, List.map_map]
    rfl
  rw [hs, List.filter_append, hpre, htail, List.nil_append, List.length_map]

/-- After an outside cut, later actual completions count the restarted killed children. -/
theorem killed_child_completion_after_cut_length (D L C : Finset Site) (hLC : L ⊆ C)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (n : ℕ)
    (hn : n ≤ domainSteps D x ω) (hout : x + position ω n ∉ C) :
    ((scanChildCompletionTimes L C x ω (domainSteps D x ω)).filter
      (fun k ↦ n < k)).length =
      (killedChildIntervals D L C (x + position ω n) (shift n ω)).length := by
  rw [scan_child_completion_after_cut_length L C hLC x ω n _ hn hout,
    killedChildIntervals_eq_scan, domainSteps_shift_before_exit D x ω hfin n hn]

end SRWTightness
