import SRWTightness.SourceKilledFirstEntranceRoots
import SRWTightness.SourceRecordTreeLeaves

namespace SRWTightness

/-- The actual source tree's ordered first-entry leaves recover the original short-root total. -/
theorem source_tree_firstEntrance_root_sum (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ k : ℕ) (hk : k < ℓ) (b : Site) (D O L E : Finset Site)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hCD : sourceExitDomain m r ℓ b k ⊆ D) (hLE : L ⊆ E) (hLO : L ⊆ O)
    (hL : L ⊆ sourceEntranceDomain m r ℓ b (ℓ - 1))
    (hE : E ⊆ sourceExitDomain m r ℓ b (ℓ - 1))
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    ((finiteRecordLeaves (ℓ - k)
      (actualFiniteWordRecord (sourceTreeEntrance m r ℓ b) (sourceTreeExit m r ℓ b)
        (firstEntranceWordOfWord (sourceExitDomain m r ℓ b (ℓ - 1)) O) (ℓ - k) x
        (killedPathWord D x ω))).map (wordMarkRootCount L E)).sum =
          (killedChildIntervals D L E x ω).length := by
  rw [source_record_tree_leaves m r ℓ k hk.le, List.map_map]
  have hi : k + (ℓ - k - 1) = ℓ - 1 := by omega
  have hn : ℓ - k - 1 + 1 = ℓ - k := by omega
  have hh := source_killed_firstEntrance_root_count_sum hF m r ℓ b hr hm k (ℓ - k - 1)
    (by omega) D O L E hCD hLE hLO (by simpa only [hi] using hL)
    (by simpa only [hi] using hE) x ω hfin
  simpa only [hi, hn, sourceTerminalRecords, Function.comp_def] using hh

end SRWTightness
