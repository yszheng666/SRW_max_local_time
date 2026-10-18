import SRWTightness.SourcePairCovarianceLower
import SRWTightness.GaussianDiagonalDensityBounds

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace SRWTightness

/-- Exact determinant factor and uniform density ratio for the actual pair covariance. -/
theorem source_pair_gaussian_density_ratio (b : Site) (t A : ℝ)
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
    let Sigma : Matrix (PairObservationIndex (I - i + 1)) _ ℝ :=
      fun j l ↦ covariance (F j) (F l) μ
    let e := fun j : Fin (I - i + 1) ↦ geometricDiskPointError b A R
      diskEnergyGapRatio (2 / Real.pi) (I + 1) (sourcePairAverageIndex I i j)
    let K := Sigma + Matrix.diagonal (pairObservationError e)
    let J := diagonalSquareRoot (pairObservationError e) * K⁻¹ *
      diagonalSquareRoot (pairObservationError e)
    K.PosDef ∧ Sigma.PosDef ∧
      (1 ≤ (Real.sqrt (1 - J).det)⁻¹ ∧
        (Real.sqrt (1 - J).det)⁻¹ ≤ Real.exp (1 / 2)) ∧
      ∀ x,
        (gaussianCovarianceDensity Sigma x).toReal /
          (gaussianCovarianceDensity K x).toReal =
          (Real.sqrt (1 - J).det)⁻¹ *
            Real.exp (-(x ⬝ᵥ ((Sigma⁻¹ - K⁻¹) *ᵥ x)) / 2) ∧
        (gaussianCovarianceDensity Sigma x).toReal ≤
          (Real.sqrt (1 - J).det)⁻¹ * (gaussianCovarianceDensity K x).toReal := by
  have hlow := source_pair_compensated_lower b t A hA ht hlog I hI i hi
    z y hz hρ hlo hhi u hu k hk
  have hblock := source_pair_observation_covariance b t A hA ht I hI i hi
    z y hz hρ hlo u hu k hk
  have he := source_pair_error_bounds b t A hA ht I hI i
  dsimp only at hlow hblock he ⊢
  let e := fun j : Fin (I - i + 1) ↦ geometricDiskPointError b A
    (Real.exp 1 * sourceLowerRadius t + 14) diskEnergyGapRatio (2 / Real.pi) (I + 1)
    (sourcePairAverageIndex I i j)
  rw [hblock, pairObservationCovarianceMatrix_compensate]
  let T := fun j : Fin (I - i + 1) ↦ sourceObservationTime t A I (j.val + 1)
  let V := fun c d : Bool ↦ covariance
    (normalizedMarkSum _ k (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi) u
      (if c then y else z))
    (normalizedMarkSum _ k (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi) u
      (if d then y else z))
    (markProductLaw (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
      (sourceReferenceIntensity (sourceLowerRadius t) 14) k)
  let K := pairObservationCovarianceMatrix T (fun _ ↦ 0) V
  have hsym : K.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro j l
    cases j <;> cases l <;>
      simp only [K, pairObservationCovarianceMatrix, star_trivial]
    · simp only [min_comm, ite_self, sub_zero]
    · exact covariance_comm _ _
  have hsmall' (j : PairObservationIndex (I - i + 1)) :
      pairObservationError e j ≤ (1 / 8 : ℝ) / 2 := by
    have hh := (Finset.single_le_sum (fun l _ ↦ he.1 l) (Finset.mem_univ j)).trans
      (he.2.trans hsmall)
    norm_num only at ⊢
    exact hh
  have hK : K.PosDef := by
    have hh := smallDiagonal_covariance_posDef K hsym (1 / 8) (by norm_num) hlow
      (fun _ ↦ 0) (by intro j; norm_num)
    simpa only [Matrix.diagonal_zero, sub_zero] using hh
  have hS := smallDiagonal_covariance_posDef K hsym (1 / 8) (by norm_num) hlow
    (pairObservationError e) hsmall'
  have hrewrite : pairObservationCovarianceMatrix T e V =
      K - Matrix.diagonal (pairObservationError e) :=
    eq_sub_iff_add_eq.mpr (pairObservationCovarianceMatrix_compensate T e V)
  change K.PosDef ∧ (pairObservationCovarianceMatrix T e V).PosDef ∧ _
  rw [hrewrite]
  have hJ := smallDiagonal_resolvent_posDef K hK (1 / 8) (by norm_num) hlow
    (pairObservationError e) he.1 hsmall'
  have hJT := smallDiagonal_resolvent_lower K hK.isUnit (1 / 8) (by norm_num) hlow
    (pairObservationError e) he.1 hsmall'
  have hdet := smallDiagonal_determinant_bounds K hK (1 / 8) (by norm_num) hlow
    (pairObservationError e) he.1 hsmall'
  have hs : (∑ j, pairObservationError e j) / (1 / 8 : ℝ) ≤ 1 / 2 := by
    have hh := he.2.trans hsmall
    linarith
  refine ⟨hK, hS, ⟨hdet.1, hdet.2.trans (Real.exp_le_exp.mpr hs)⟩, ?_⟩
  intro x
  have hsquare := diagonalSquareRoot_square (pairObservationError e) he.1
  have hr := gaussianCovarianceDensity_sub_square_ratio K
    (diagonalSquareRoot (pairObservationError e)) hK
    (by rw [hsquare]; exact hS) hJ x
  rw [hsquare] at hr
  have hKT : Kᵀ = K := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  have hq := covariance_diagonal_inverse_difference_bounds K (pairObservationError e)
    he.1 hK.isUnit hKT hJ hJT x
  have hp := gaussianCovarianceDensity_toReal_pos K hK x
  refine ⟨hr, ?_⟩
  apply (div_le_iff₀ hp).mp
  rw [hr]
  apply mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
  exact Real.exp_le_one_iff.mpr (by linarith [hq.1])

end SRWTightness
