import SRWTightness.FirstEntranceAdmissibleRoots
import SRWTightness.SourceNestedWordFlatten

namespace SRWTightness

/-- First-entry marks of all terminal source words retain the direct short-root total. -/
theorem source_terminal_firstEntrance_root_count_sum (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ : ℕ) (b : Site) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (k n : ℕ) (hn : k + n + 1 ≤ ℓ) (O L E : Finset Site) (hLE : L ⊆ E) (hLO : L ⊆ O)
    (hL : L ⊆ sourceEntranceDomain m r ℓ b (k + n))
    (hE : E ⊆ sourceExitDomain m r ℓ b (k + n))
    (x : Site) (w : PathWord)
    (hend : x + position (wordPath w) w.length ∉ sourceExitDomain m r ℓ b k) :
    ((terminalWordRecords (sourceExcursionLevels m r ℓ b k (n + 1)) x w).map
      (fun p ↦ wordMarkRootCount L E (firstEntranceWordOfWord
        (sourceExitDomain m r ℓ b (k + n)) O p.1 p.2))).sum =
        (wordChildIntervals L E x w).length := by
  rw [source_nested_word_flatten hF m r ℓ b hr hm k n hn x w hend]
  have hout : x + position (wordPath w) w.length ∉
      sourceExitDomain m r ℓ b (k + n) :=
    fun h ↦ hend (sourceExitDomain_antitone m r ℓ b hr hm (by omega) h)
  have hh := word_child_firstEntrance_root_count_sum hF
    (sourceEntranceDomain m r ℓ b (k + n)) (sourceExitDomain m r ℓ b (k + n)) O L E
    (sourceEntranceDomain_subset_exit m r ℓ b (k + n) hr hm hn) hLE hL hLO hE x w hout
  simpa only [wordChildRecords, List.map_map, Function.comp_def] using hh

end SRWTightness
