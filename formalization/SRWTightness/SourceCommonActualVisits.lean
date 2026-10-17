import SRWTightness.MarkSumGenerating
import SRWTightness.SourceCommonActualForest
import SRWTightness.SourceSingleRootVisits
import SRWTightness.TerminalListVisitSum

open scoped BigOperators
namespace SRWTightness

/-- The decoded common leaf marks sum to the original disk-killed local time. -/
theorem source_common_actual_mark_visits (t : ℝ) (b : Site) (K : Finset Site)
    (j : ℕ) (ω : Sample) (r : FiniteExcursionRecord (Mark K) j)
    (hr : sourceCommonActualForest t b K j ω = [r])
    (hm : 16 ≤ sourceCommonPairInnerRadius t j)
    (hK : K ⊆ translateFinset b (diskFinset (sourceCommonPairInnerRadius t j - 16)))
    (hroot : sourceExitDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b 0 ⊆
      diskFinset (Real.exp t)) (hfin : domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤)
    (y : K) :
    let k := geometricGWPopulation (finiteRecordPopulationList j r) j
    (sumMarks K k (terminalListSamples 0 k (finiteRecordLeaves j r)) y : ℝ) =
      (domainLocalTime (diskFinset (Real.exp t)) 0 y ω : ℝ) := by
  rw [source_common_actual_forest_eq] at hr
  have hbuf : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  have hv := source_single_root_mark_visits (sourceCommonPairInnerRadius t j) 1 j b
    (diskFinset (Real.exp t)) K 0 (by norm_num) (by rw [hbuf]; linarith)
    (by simpa only [hbuf, show (sourceCommonPairInnerRadius t j - 14 - 2) =
      sourceCommonPairInnerRadius t j - 16 by ring] using hK)
    hroot ω hfin r hr y
  dsimp only
  calc
    _ = ∑ i : Fin (geometricGWPopulation (finiteRecordPopulationList j r) j),
        (terminalListSamples 0 _ (finiteRecordLeaves j r) i y : ℝ) := by
      simp only [sumMarks, Nat.cast_sum]
    _ = ((((finiteRecordLeaves j r).map (fun v ↦ v y)).sum : ℕ) : ℝ) :=
      terminal_tree_visit_sum K j r y
    _ = _ := by rw [hv]

end SRWTightness
