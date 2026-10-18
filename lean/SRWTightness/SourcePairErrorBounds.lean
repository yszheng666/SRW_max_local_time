import SRWTightness.PairObservationCompensation
import SRWTightness.SourceGaussianErrorBounds

namespace SRWTightness

/-- Retaining fewer averages preserves the uniform correction trace bound. -/
theorem source_pair_error_bounds (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) :
    let e := fun j : Fin (I - i + 1) ↦ geometricDiskPointError b A
      (Real.exp 1 * sourceLowerRadius t + 14) diskEnergyGapRatio (2 / Real.pi) (I + 1)
      (sourcePairAverageIndex I i j)
    (∀ j, 0 ≤ pairObservationError e j) ∧
      (∑ j, pairObservationError e j) ≤ (diskEquilibriumWeightConstant / A) / (2 / Real.pi) := by
  classical
  have he := source_gaussian_error_bounds b t A hA ht I hI
  dsimp only at he ⊢
  refine ⟨pairObservationError_nonneg _ (fun j ↦ he.1 _), ?_⟩
  rw [pairObservationError_sum]
  have hinj : Function.Injective (sourcePairAverageIndex I i) := by
    intro j l h
    apply Fin.ext
    exact congrArg (fun a : Fin ((I + 1) + 1) ↦ a.val) h
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.image (sourcePairAverageIndex I i) Finset.univ))
    (fun j _ _ ↦ he.1 j)
  rw [Finset.sum_image (fun j _ l _ h ↦ hinj h)] at hs
  exact hs.trans he.2.1

end SRWTightness
