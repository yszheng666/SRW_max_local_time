import SRWTightness.SourcePairGaussianEndpointInternal

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual residual covariance is h times the identity up to one uniform entrywise error. -/
theorem source_pair_residual_entrywise
    (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 3 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let m := sourceLowerRadius t
    let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity m 14
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α (2 / Real.pi) u
    let V := fun c d : Bool ↦ covariance (F (if c then y else z)) (F (if d then y else z)) μ
    let v := sourceObservationTime t A I (I - i + 1)
    let R := pairResidualMatrix (V false false) (V true true) (V false true) v
    ∀ a b, |R a b - Matrix.diagonal
      (fun _ : Fin 2 ↦ sourceLowerTime m - v) a b| ≤ sourcePairResidualError := by
  obtain ⟨ha, hma, hMD, hKM, hcap⟩ :=
    source_pair_observation_geometry b t A hA ht I hI i hi
  have hm := (sourceScaleThreshold_conditions t A
    (diskGaussianMinimumRadius_ge_four.trans
      (diskPointGaussianMinimumRadius_ge_base.trans hA))
    ((le_max_left _ _).trans ht)).2.2.1
  have hb := source_pair_covariance_bounds b (sourceLowerRadius t) 14
    (A * diskEnergyGapRatio ^ i) (4 * diskEnergyGapRatio)
    (by linarith) (by norm_num) (by linarith) hma _ hMD z y hz hρ hlo hhi
    u hu hcap k hk
  have hbound : max sourcePairVarianceError
      (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 +
        Real.log (4 * diskEnergyGapRatio)) ≤ sourcePairResidualError := le_max_right _ _
  dsimp only
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [source_observation_time_at_radius b t A I i hi]
  exact pairResidualMatrix_entrywise _ _ _ _ _ _
    (hb.1.trans ((le_max_left _ _).trans hbound))
    (hb.2.1.trans ((le_max_left _ _).trans hbound))
    (hb.2.2.trans ((le_max_right _ _).trans hbound))

/-- The same residual dominates one half of its source time times the identity. -/
theorem source_pair_residual_quadratic_lower
    (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 3 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let m := sourceLowerRadius t
    let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity m 14
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α (2 / Real.pi) u
    let V := fun c d : Bool ↦ covariance (F (if c then y else z)) (F (if d then y else z)) μ
    let v := sourceObservationTime t A I (I - i + 1)
    let R := pairResidualMatrix (V false false) (V true true) (V false true) v
    ∀ x : Fin 2 → ℝ, ((sourceLowerTime m - v) / 2) * (∑ j, x j ^ 2) ≤
      x ⬝ᵥ (R *ᵥ x) := by
  have he := source_pair_residual_entrywise b t A hA ht hlog I hI i hi
    z y hz hρ hlo hhi u hu k hk
  have hC : 0 ≤ sourcePairResidualError := le_max_left _ _
  have hr := source_pair_residual_time b t A sourcePairResidualError hA ht hC
    (by linarith) I hI i hi
  dsimp only at he ⊢
  intro x
  apply entrywise_covariance_lower _
    (Matrix.diagonal (fun _ : Fin 2 ↦ sourceLowerTime (sourceLowerRadius t) -
      sourceObservationTime t A I (I - i + 1))) _ sourcePairResidualError hC he
  · intro y
    simp only [dotProduct, Matrix.mulVec_diagonal]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    nlinarith
  · simp only [Fintype.card_fin, Nat.cast_ofNat]
    linarith [hr.2]

end SRWTightness
