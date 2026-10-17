import SRWTightness.SourcePairCompensatedLower
import SRWTightness.SourcePairErrorBounds
import SRWTightness.SmallDiagonalCovariancePositive

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The full actual pair covariance retains a one-sixteenth lower bound after diagonal correction. -/
theorem source_pair_covariance_lower (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 3 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A)
    (hsmall : (diskEquilibriumWeightConstant / A) / (2 / Real.pi) ≤ 1 / 16)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let R := Real.exp 1 * sourceLowerRadius t + 14
    let D := translateFinset b (diskFinset R)
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := markProductLaw D M α k
    let F := fun j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j)
    ∀ x : PairObservationIndex (I - i + 1) → ℝ,
      (1 / 16 : ℝ) * (∑ j, x j ^ 2) ≤
        x ⬝ᵥ ((fun j l ↦ covariance (F j) (F l) μ) *ᵥ x) := by
  have hK := source_pair_compensated_lower b t A hA ht hlog I hI i hi
    z y hz hρ hlo hhi u hu k hk
  have hblock := source_pair_observation_covariance b t A hA ht I hI i hi
    z y hz hρ hlo u hu k hk
  have he := source_pair_error_bounds b t A hA ht I hI i
  dsimp only at hK hblock he ⊢
  intro x
  rw [hblock]
  let e := fun j : Fin (I - i + 1) ↦ geometricDiskPointError b A
    (Real.exp 1 * sourceLowerRadius t + 14) diskEnergyGapRatio (2 / Real.pi) (I + 1)
    (sourcePairAverageIndex I i j)
  have hesmall (j : PairObservationIndex (I - i + 1)) :
      pairObservationError e j ≤ (1 / 8 : ℝ) / 2 := by
    have hh := (Finset.single_le_sum (fun l _ ↦ he.1 l) (Finset.mem_univ j)).trans
      (he.2.trans hsmall)
    norm_num only at ⊢
    exact hh
  rw [show pairObservationCovarianceMatrix _ e _ =
      pairObservationCovarianceMatrix _ (fun _ ↦ 0) _ - Matrix.diagonal (pairObservationError e)
      from eq_sub_iff_add_eq.mpr (pairObservationCovarianceMatrix_compensate _ e _)]
  convert smallDiagonal_covariance_lower _ (1 / 8) hK (pairObservationError e) hesmall x
    using 1 <;> norm_num

end SRWTightness
