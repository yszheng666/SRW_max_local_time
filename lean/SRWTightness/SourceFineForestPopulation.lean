import SRWTightness.SourceForwardCountConsistency
import SRWTightness.SourceLongFineRecord
import SRWTightness.ForestPopulationError

open MeasureTheory
namespace SRWTightness

/-- The actual ordered fine forest rooted at all level-nu short excursions of the original walk. -/
noncomputable def sourceActualFineForest (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    (ω : Sample) :
    List (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))) :=
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  killedChildRecords (diskFinset (Real.exp t)) (sourceEntranceDomain m 1 ℓ b ν)
    (sourceExitDomain m 1 ℓ b ν) 0 (sourceLongFineRecord t b K ν) ω

/-- Every fine-forest population is an original manuscript count, simultaneously at all depths. -/
theorem source_fine_forest_population (hF : TwoLevelWordFlatteningInput)
    (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    (hm : 16 ≤ sourceLowerRadius t)
    (hν : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t))
    (hD : sourceExitDomain (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b 0 ⊆ diskFinset (Real.exp t)) :
    ∀ᵐ ω ∂pathLaw, ∀ j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1),
      forestLevelPopulation (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        (sourceActualFineForest t b K ν ω) j =
          sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (j + 1)) ω := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro hj
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let i := ℓ - (j + 1)
  have hki : ν ≤ i := by dsimp [i, ℓ, m]; omega
  have hi : i < ℓ := by dsimp [i, ℓ, m]; omega
  have heq : ℓ - (i + 1) = j := by dsimp [i, ℓ, m]; omega
  have hc := source_forward_count_consistency hF m 1 ℓ b (by norm_num)
    (by norm_num [sourceRecordBuffer]; exact hm) ν i hki (by omega)
    (diskFinset (Real.exp t)) 0 hD
  filter_upwards [hc] with ω hω
  have hp := source_forest_population m 1 ℓ ν i hki hi b (diskFinset (Real.exp t)) 0
    (wordOccupationMark K) ω
  rw [heq, hω] at hp
  exact hp

end SRWTightness
