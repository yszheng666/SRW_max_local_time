import SRWTightness.SourcePairAverageIndex
import SRWTightness.SourceObservationCovariance

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The retained average covariance is the corresponding submatrix of the already proved K-E matrix. -/
theorem source_pair_average_block (b : Site) (t A : ℝ)
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
      (brownianTimeMatrix (sourceObservationTime t A I) ((I + 1) + 1) -
        Matrix.diagonal (geometricDiskPointError b A R diskEnergyGapRatio
          (2 / Real.pi) (I + 1)))
        (sourcePairAverageIndex I i j) (sourcePairAverageIndex I i l) := by
  obtain ⟨J, hJ, z, hz, hcov⟩ := source_observation_covariance b t A hA ht
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  have hh := hcov k u hu hk (sourcePairAverageIndex I i j) (sourcePairAverageIndex I i l)
  rw [sourcePairAverageIndex_observation, sourcePairAverageIndex_observation] at hh
  exact hh

end SRWTightness
