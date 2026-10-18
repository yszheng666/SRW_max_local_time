import SRWTightness.SourceSingleRootFirstEntrance
import SRWTightness.SourceCommonOrderedForest

namespace SRWTightness

/-- A selected actual common record retains the short-root total in its ordered leaf marks. -/
theorem source_common_ordered_leaf_roots (hF : TwoLevelWordFlatteningInput)
    (t : ℝ) (b : Site) (O L E : Finset Site) (j : ℕ) (ω : Sample)
    (r : FiniteExcursionRecord WordMark j)
    (hr : sourceCommonOrderedForest t b O j ω = [r])
    (hm : 16 ≤ sourceCommonPairInnerRadius t j) (hLE : L ⊆ E) (hLO : L ⊆ O)
    (hL : L ⊆ sourceEntranceDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b j)
    (hE : E ⊆ sourceExitDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b j)
    (hroot : sourceExitDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b 0 ⊆
      diskFinset (Real.exp t)) (hfin : domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤) :
    ((finiteRecordLeaves j r).map (wordMarkRootCount L E)).sum =
      (killedChildIntervals (diskFinset (Real.exp t)) L E 0 ω).length := by
  rw [source_common_ordered_forest_eq] at hr
  have hbuf : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  have he := source_tree_exit_growing (sourceCommonPairInnerRadius t j) 1 (j + 1) b 0
    (by omega)
  simp only [sourceTreeExit, Nat.zero_add, Nat.add_sub_cancel, hbuf] at he
  rw [← he] at hr
  exact source_single_root_firstEntrance_sum hF (sourceCommonPairInnerRadius t j) 1 j b
    (diskFinset (Real.exp t)) O L E 0 (by norm_num) (by rw [hbuf]; linarith)
    hroot hLE hLO hL hE ω hfin r hr

end SRWTightness
