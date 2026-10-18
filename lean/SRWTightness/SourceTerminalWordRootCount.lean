import SRWTightness.WordRootCountFlatten
import SRWTightness.SourceNestedWordFlatten

namespace SRWTightness

/-- Direct short-root counts equal the sum over all terminal source words, with multiplicity. -/
theorem source_terminal_word_root_count_sum (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ : ℕ) (b : Site) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (k n : ℕ) (hn : k + n + 1 ≤ ℓ) (L E : Finset Site) (hLE : L ⊆ E)
    (hL : L ⊆ sourceEntranceDomain m r ℓ b (k + n))
    (hE : E ⊆ sourceExitDomain m r ℓ b (k + n))
    (x : Site) (w : PathWord)
    (hend : x + position (wordPath w) w.length ∉ sourceExitDomain m r ℓ b k) :
    ((terminalWordRecords (sourceExcursionLevels m r ℓ b k (n + 1)) x w).map
      (fun p ↦ wordMarkRootCount L E (some p))).sum =
        (wordChildIntervals L E x w).length := by
  rw [source_nested_word_flatten hF m r ℓ b hr hm k n hn x w hend]
  have hout : x + position (wordPath w) w.length ∉
      sourceExitDomain m r ℓ b (k + n) :=
    fun h ↦ hend (sourceExitDomain_antitone m r ℓ b hr hm (by omega) h)
  have hh := word_child_root_count_sum hF
    (sourceEntranceDomain m r ℓ b (k + n)) (sourceExitDomain m r ℓ b (k + n)) L E
    (sourceEntranceDomain_subset_exit m r ℓ b (k + n) hr hm hn) hLE hL hE x w hout
  simpa only [wordChildRecords, List.map_map, Function.comp_def] using hh

end SRWTightness
