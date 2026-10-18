import SRWTightness.SourceUpperBlockRootCount
import SRWTightness.ForestPopulationError

namespace SRWTightness

/-- Remaining tree depth below the selected actual upper root. -/
noncomputable def sourceUpperBlockForestDepth (t : ℝ) (b : Site) : ℕ :=
  sourceRootDepth (Real.exp t) (sourceUpperRadius t) - (sourceUpperBlockRoot t b + 1)

/-- Actual chronological upper roots, retaining all internal records and terminal observations. -/
noncomputable def sourceUpperBlockForest {M : Type*} (t : ℝ) (b : Site)
    (F : Site → PathWord → M) (ω : Sample) :
    List (FiniteExcursionRecord M (sourceUpperBlockForestDepth t b)) :=
  killedChildRecords (diskFinset (Real.exp t))
    (sourceUpperBlockInner t (sourceUpperBlockRoot t b) b)
    (sourceUpperBlockOuter t (sourceUpperBlockRoot t b) b) 0
    (actualFiniteWordRecord
      (sourceTreeEntrance (sourceUpperRadius t)
        (upperTerminalFineRadius (sourceUpperLogRadius t))
        (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) b)
      (sourceTreeExit (sourceUpperRadius t)
        (upperTerminalFineRadius (sourceUpperLogRadius t))
        (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) b)
      F (sourceUpperBlockForestDepth t b)) ω

/-- The actual forward generation count in an upper block. -/
noncomputable def sourceUpperBlockCount (t : ℝ) (b : Site) (j : ℕ) (ω : Sample) : ℕ :=
  sourceForwardRecordCount (sourceUpperRadius t)
    (upperTerminalFineRadius (sourceUpperLogRadius t))
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (sourceUpperBlockRoot t b) j b
    (diskFinset (Real.exp t)) 0 ω

/-- Forward root count agrees with the complete root count already used in the cap event. -/
theorem sourceUpperBlockCount_root (t : ℝ) (b : Site) (ω : Sample) :
    sourceUpperBlockCount t b (sourceUpperBlockRoot t b) ω =
      sourceUpperBlockRootCount t b ω := by
  unfold sourceUpperBlockCount
  rw [source_forward_root_count]
  rfl

/-- Retaining internal and terminal records preserves the actual number of roots. -/
theorem sourceUpperBlockForest_length {M : Type*} (t : ℝ) (b : Site)
    (F : Site → PathWord → M) (ω : Sample) :
    (sourceUpperBlockForest t b F ω).length = sourceUpperBlockRootCount t b ω := by
  simp only [sourceUpperBlockForest, killedChildRecords, wordChildRecords, List.length_map]
  rfl

/-- Each forest population is exactly the corresponding forward manuscript generation count. -/
theorem source_upper_block_forest_population {M : Type*} (t : ℝ) (b : Site)
    (F : Site → PathWord → M) (ω : Sample) (j : ℕ)
    (hkj : sourceUpperBlockRoot t b ≤ j)
    (hj : j < sourceRootDepth (Real.exp t) (sourceUpperRadius t)) :
    forestLevelPopulation (sourceUpperBlockForestDepth t b) (sourceUpperBlockForest t b F ω)
      (sourceRootDepth (Real.exp t) (sourceUpperRadius t) - (j + 1)) =
        sourceUpperBlockCount t b j ω := by
  exact source_forest_population (sourceUpperRadius t)
    (upperTerminalFineRadius (sourceUpperLogRadius t))
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (sourceUpperBlockRoot t b) j
    hkj hj b (diskFinset (Real.exp t)) 0 F ω

/-- The actual root cap and later count caps control every forest generation. -/
theorem source_upper_block_forest_population_cap {M : Type*} (t : ℝ) (b : Site)
    (F : Site → PathWord → M) (ω : Sample)
    (hk : sourceUpperBlockRoot t b < sourceRootDepth (Real.exp t) (sourceUpperRadius t))
    (hroot : (sourceUpperBlockRootCount t b ω : ℝ) ≤ t ^ 2)
    (hcounts : ∀ j : ℕ, sourceUpperBlockRoot t b < j → j ≤ sourceUpperCoarseDepth t →
      (sourceUpperBlockCount t b j ω : ℝ) ≤ 16 * t ^ 2) :
    ∀ i ≤ sourceUpperBlockForestDepth t b,
      (forestLevelPopulation (sourceUpperBlockForestDepth t b)
        (sourceUpperBlockForest t b F ω) i : ℝ) ≤ 16 * t ^ 2 := by
  intro i hi
  let ℓ := sourceRootDepth (Real.exp t) (sourceUpperRadius t)
  let j := ℓ - (i + 1)
  have hi' : i ≤ ℓ - (sourceUpperBlockRoot t b + 1) := hi
  have hkj : sourceUpperBlockRoot t b ≤ j := by dsimp [j]; omega
  have hj : j < ℓ := by dsimp [j]; omega
  have hidx : ℓ - (j + 1) = i := by dsimp [j]; omega
  have hp := source_upper_block_forest_population t b F ω j hkj hj
  change forestLevelPopulation _ _ (ℓ - (j + 1)) = _ at hp
  rw [hidx] at hp
  rw [hp]
  by_cases heq : j = sourceUpperBlockRoot t b
  · rw [heq, sourceUpperBlockCount_root]
    nlinarith [sq_nonneg t]
  · exact hcounts j (by omega) (by change j ≤ ℓ - 1; omega)

end SRWTightness
