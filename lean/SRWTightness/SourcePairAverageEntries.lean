import SRWTightness.SourcePairAverageBlock

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The retained average covariance is Brownian covariance minus its diagonal correction. -/
theorem source_pair_average_entries (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ))
    (j l : Fin (I - i + 1)) :
    let R := Real.exp 1 * sourceLowerRadius t + 14
    let D := translateFinset b (diskFinset R)
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let S := fun a ↦ normalizedEquilibriumAverage D M (sourcePairAverageFamily b A I i a)
      k α (2 / Real.pi) u
    covariance (S j) (S l) (markProductLaw D M α k) =
      min (sourceObservationTime t A I (j.val + 1))
        (sourceObservationTime t A I (l.val + 1)) -
      (if j = l then geometricDiskPointError b A R diskEnergyGapRatio
        (2 / Real.pi) (I + 1) (sourcePairAverageIndex I i j) else 0) := by
  have hh := source_pair_average_block b t A hA ht I hI i u hu k hk j l
  dsimp only at hh ⊢
  simpa only [Matrix.sub_apply, brownianTimeMatrix, Matrix.of_apply, Matrix.diagonal_apply,
    sourcePairAverageIndex, Fin.val_castSucc, Fin.ext_iff] using hh

end SRWTightness
