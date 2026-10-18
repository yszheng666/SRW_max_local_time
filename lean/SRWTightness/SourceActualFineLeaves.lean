import SRWTightness.SourceForestLeaves
import SRWTightness.SourceTerminalRecordConsistency
import SRWTightness.SourceFineForestPopulation

open MeasureTheory
namespace SRWTightness

/-- Cutting the original forest at any admissible root level preserves its full ordered terminal marks. -/
theorem source_actual_fine_leaves (hF : TwoLevelWordFlatteningInput)
    (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    (hm : 16 ≤ sourceLowerRadius t)
    (hν : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t))
    (hD : sourceExitDomain (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b 0 ⊆ diskFinset (Real.exp t)) :
    ∀ᵐ ω ∂pathLaw,
      (sourceActualFineForest t b K ν ω).flatMap (finiteRecordLeaves
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))) =
      (sourceActualForest t b K ω).flatMap (finiteRecordLeaves
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1)) := by
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  have hk : ν < ℓ := by dsimp [ℓ, m]; omega
  have hm' : sourceRecordBuffer 1 + 2 ≤ m := by norm_num [sourceRecordBuffer]; exact hm
  filter_upwards [source_terminal_record_consistency hF m 1 ℓ ν b (by norm_num) hm'
    hk (diskFinset (Real.exp t)) 0 hD] with ω hω
  have h₁ := source_forest_leaves m 1 ℓ ν hk b (diskFinset (Real.exp t)) 0 (wordOccupationMark K) ω
  have h₀ := source_forest_leaves m 1 ℓ 0 (by omega) b (diskFinset (Real.exp t)) 0 (wordOccupationMark K) ω
  exact h₁.trans ((congrArg (List.map (fun p : Site × PathWord ↦ wordOccupationMark K p.1 p.2)) hω).trans h₀.symm)

end SRWTightness
