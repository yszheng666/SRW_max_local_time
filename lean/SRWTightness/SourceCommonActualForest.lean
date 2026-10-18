import SRWTightness.SourceCommonPairRebase
import SRWTightness.SourceGrowingRecordIdentity
import SRWTightness.SourceWalkSuccessEvent

namespace SRWTightness

/-- Rebasing a common prefix does not change any chronological forward count. -/
theorem sourceForwardRecordCount_rebase (m buffer : ℝ) (ℓ j k i : ℕ) (b : Site)
    (D : Finset Site) (x : Site) (ω : Sample) :
    sourceForwardRecordCount (sourceRecordRadius m ℓ (j + 1)) buffer (j + 1) k i b D x ω =
      sourceForwardRecordCount m buffer ℓ k i b D x ω := by
  simp only [sourceForwardRecordCount, sourceExcursionLevels_rebase]

/-- Actual common-prefix records, with terminal observations retained at the common radius. -/
noncomputable def sourceCommonActualForest (t : ℝ) (b : Site) (K : Finset Site)
    (j : ℕ) (ω : Sample) : List (FiniteExcursionRecord (Mark K) j) :=
  let m := sourceCommonPairInnerRadius t j
  killedChildRecords (diskFinset (Real.exp t)) (growingRecordEntrance b m 14 j)
    (growingRecordExit b m 14 j) 0
    (actualFiniteWordRecord (growingRecordEntrance b m 14) (growingRecordExit b m 14)
      (wordOccupationMark K) j) ω

/-- The geometric common record is exactly the rebased source record, including its root domains. -/
theorem source_common_actual_forest_eq (t : ℝ) (b : Site) (K : Finset Site)
    (j : ℕ) (ω : Sample) :
    sourceCommonActualForest t b K j ω =
      killedChildRecords (diskFinset (Real.exp t))
        (sourceEntranceDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b 0)
        (sourceExitDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b 0) 0
        (actualFiniteWordRecord (sourceTreeEntrance (sourceCommonPairInnerRadius t j) 1 (j + 1) b)
          (sourceTreeExit (sourceCommonPairInnerRadius t j) 1 (j + 1) b)
          (wordOccupationMark K) j) ω := by
  have hbuf : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  have hent := source_tree_entrance_growing (sourceCommonPairInnerRadius t j) 1 (j + 1) b j (by omega)
  have hexit := source_tree_exit_growing (sourceCommonPairInnerRadius t j) 1 (j + 1) b j (by omega)
  simp only [sourceTreeEntrance, sourceTreeExit, Nat.sub_self, hbuf] at hent hexit
  rw [hent, hexit, source_actual_tree_growing _ _ _ _ _ _ (by omega), hbuf]
  rfl

/-- Every common-prefix population is the original walk's chronological segment count. -/
theorem source_common_actual_forest_population (t : ℝ) (b : Site) (K : Finset Site)
    (j : ℕ) (ω : Sample) (r : FiniteExcursionRecord (Mark K) j)
    (hr : sourceCommonActualForest t b K j ω = [r]) (i : ℕ) (hi : i ≤ j) :
    geometricGWPopulation (finiteRecordPopulationList j r) i = sourceActualCount t b i ω := by
  rw [source_common_actual_forest_eq] at hr
  have hp := source_single_forest_gw_population (sourceCommonPairInnerRadius t j) 1 (j + 1)
    (by omega) b (diskFinset (Real.exp t)) 0 (wordOccupationMark K) ω r hr i (by omega)
  change geometricGWPopulation (finiteRecordPopulationList j r) i =
    sourceForwardRecordCount (sourceCommonPairInnerRadius t j) 1 (j + 1) 0 i b
      (diskFinset (Real.exp t)) 0 ω at hp
  rw [sourceCommonPairInnerRadius, sourceForwardRecordCount_rebase] at hp
  exact hp

end SRWTightness
