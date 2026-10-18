import SRWTightness.SourceCommonActualForest
import SRWTightness.FirstEntranceWordFunctional
import SRWTightness.SourceEarlyPrefixEvent
import SRWTightness.SourceGrowingRecordIdentity
import SRWTightness.SourceWalkSuccessEvent

namespace SRWTightness

/-- Actual common-prefix records, with terminal observations retained at the common radius. -/
noncomputable def sourceCommonOrderedForest (t : ℝ) (b : Site) (K : Finset Site)
    (j : ℕ) (ω : Sample) : List (FiniteExcursionRecord WordMark j) :=
  let m := sourceCommonPairInnerRadius t j
  killedChildRecords (diskFinset (Real.exp t)) (growingRecordEntrance b m 14 j)
    (growingRecordExit b m 14 j) 0
    (actualFiniteWordRecord (growingRecordEntrance b m 14) (growingRecordExit b m 14)
      (firstEntranceWordOfWord
        (growingRecordExit b (sourceCommonPairInnerRadius t j) 14 0) K) j) ω

/-- The geometric common record is exactly the rebased source record, including its root domains. -/
theorem source_common_ordered_forest_eq (t : ℝ) (b : Site) (K : Finset Site)
    (j : ℕ) (ω : Sample) :
    sourceCommonOrderedForest t b K j ω =
      killedChildRecords (diskFinset (Real.exp t))
        (sourceEntranceDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b 0)
        (sourceExitDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b 0) 0
        (actualFiniteWordRecord (sourceTreeEntrance (sourceCommonPairInnerRadius t j) 1 (j + 1) b)
          (sourceTreeExit (sourceCommonPairInnerRadius t j) 1 (j + 1) b)
          (firstEntranceWordOfWord
        (growingRecordExit b (sourceCommonPairInnerRadius t j) 14 0) K) j) ω := by
  have hbuf : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  have hent := source_tree_entrance_growing
    (sourceCommonPairInnerRadius t j) 1 (j + 1) b j (by omega)
  have hexit := source_tree_exit_growing
    (sourceCommonPairInnerRadius t j) 1 (j + 1) b j (by omega)
  simp only [sourceTreeEntrance, sourceTreeExit, Nat.sub_self, hbuf] at hent hexit
  rw [hent, hexit, source_actual_tree_growing _ _ _ _ _ _ (by omega), hbuf]
  rfl

/-- Every common-prefix population is the original walk's chronological segment count. -/
theorem source_common_ordered_forest_population (t : ℝ) (b : Site) (K : Finset Site)
    (j : ℕ) (ω : Sample) (r : FiniteExcursionRecord WordMark j)
    (hr : sourceCommonOrderedForest t b K j ω = [r]) (i : ℕ) (hi : i ≤ j) :
    geometricGWPopulation (finiteRecordPopulationList j r) i = sourceActualCount t b i ω := by
  rw [source_common_ordered_forest_eq] at hr
  have hp := source_single_forest_gw_population (sourceCommonPairInnerRadius t j) 1 (j + 1)
    (by omega) b (diskFinset (Real.exp t)) 0 (firstEntranceWordOfWord
        (growingRecordExit b (sourceCommonPairInnerRadius t j) 14 0) K) ω r hr i (by omega)
  change geometricGWPopulation (finiteRecordPopulationList j r) i =
    sourceForwardRecordCount (sourceCommonPairInnerRadius t j) 1 (j + 1) 0 i b
      (diskFinset (Real.exp t)) 0 ω at hp
  rw [sourceCommonPairInnerRadius, sourceForwardRecordCount_rebase] at hp
  exact hp

/-- The common root list retains the original walk's level-zero count. -/
theorem source_common_ordered_forest_length (t : ℝ) (b : Site) (K : Finset Site)
    (j : ℕ) (ω : Sample) :
    (sourceCommonOrderedForest t b K j ω).length = sourceActualCount t b 0 ω := by
  rw [source_common_ordered_forest_eq]
  have hc : sourceActualCount t b 0 ω =
      sourceForwardRecordCount (sourceCommonPairInnerRadius t j) 1 (j + 1) 0 0 b
        (diskFinset (Real.exp t)) 0 ω := by
    rw [sourceCommonPairInnerRadius, sourceForwardRecordCount_rebase]
    rfl
  rw [hc, source_forward_root_count]
  simp only [killedChildRecords, wordChildRecords, List.length_map]

/-- The original prefix event selects one actual common record with exactly the original barrier. -/
theorem source_common_ordered_prefix (t : ℝ) (b : Site) (K : Finset Site) (j : ℕ)
    (ω : Sample) (hω : ω ∈ sourceEarlyPrefixEvent t b j) :
    ∃ r : FiniteExcursionRecord WordMark j, sourceCommonOrderedForest t b K j ω = [r] ∧
      ∀ k : ℕ, 0 < k → k ≤ j →
      geometricGWHeight (finiteRecordPopulationList j r) k ≤
        4 + sourceBarrierSlope t * k -
          (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ) := by
  have hlen := (source_common_ordered_forest_length t b K j ω).trans hω.1
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨r, hr, ?_⟩
  intro k hk hkj
  unfold geometricGWHeight
  rw [source_common_ordered_forest_population t b K j ω r hr k hkj]
  exact hω.2 k hk hkj

end SRWTightness
