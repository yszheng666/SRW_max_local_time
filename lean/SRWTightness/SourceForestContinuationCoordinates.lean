import SRWTightness.ExternalMarkedGWForestJoint
import SRWTightness.SourceFineForestPopulation
import SRWTightness.SourceRootGWHorizon
import SRWTightness.SourceContinuationProbability

open MeasureTheory
namespace SRWTightness

/-- The forest GW coordinates read the existing populations in chronological order. -/
theorem forest_gw_population {M : Type*} (n : ℕ) (rs : List (FiniteExcursionRecord M n))
    (j : ℕ) (hj : j ≤ n) :
    geometricGWPopulation (forestPopulationList n rs) j = forestLevelPopulation n rs (n - j) := by
  unfold geometricGWPopulation forestPopulationList
  rw [List.getElem?_reverse (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn, Nat.add_sub_cancel, List.getElem?_ofFn,
    dif_pos (show n - j < n + 1 by omega), Option.getD_some]

/-- The terminal mark list counts every terminal individual across the complete forest. -/
theorem forest_leaves_length {M : Type*} (n : ℕ) (rs : List (FiniteExcursionRecord M n)) :
    (rs.flatMap (finiteRecordLeaves n)).length = forestLevelPopulation n rs 0 := by
  simp only [List.length_flatMap, finiteRecordLeaves_length, forestLevelPopulation]

/-- Actual fine depth and the source continuation horizon agree, including natural truncation. -/
theorem source_fine_continuation_depth (t : ℝ) (ν : ℕ) :
    sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1) = sourceContinuationLength t ν := by
  unfold sourceContinuationLength
  rw [← source_root_gw_horizon]
  omega

/-- All chronological populations in the actual fine forest are the shifted original source counts. -/
theorem source_fine_continuation_population (hF : TwoLevelWordFlatteningInput)
    (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    (hm : 16 ≤ sourceLowerRadius t)
    (hν : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t))
    (hD : sourceExitDomain (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b 0 ⊆ diskFinset (Real.exp t)) :
    ∀ᵐ ω ∂pathLaw, ∀ j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1),
      geometricGWPopulation (forestPopulationList
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        (sourceActualFineForest t b K ν ω)) j = sourceActualCount t b (ν + j) ω := by
  filter_upwards [source_fine_forest_population hF t b K ν hm hν hD] with ω hω
  intro j hj
  rw [forest_gw_population _ _ j hj, hω _ (Nat.sub_le _ _)]
  congr 2
  omega

end SRWTightness
