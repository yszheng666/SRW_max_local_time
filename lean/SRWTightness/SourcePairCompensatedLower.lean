import SRWTightness.PairCompensatedLower
import SRWTightness.SourcePairBrownianLower
import SRWTightness.SourcePairNodeResidualLower
import SRWTightness.PairResidualQuadratic

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual compensated pair observation covariance has a uniform one-eighth lower bound. -/
theorem source_pair_compensated_lower (b : Site) (t A : ℝ)
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
    ∀ x : PairObservationIndex (I - i + 1) → ℝ,
      (1 / 8 : ℝ) * (∑ j, x j ^ 2) ≤ x ⬝ᵥ
        (pairObservationCovarianceMatrix (fun j ↦ sourceObservationTime t A I (j.val + 1))
          (fun _ ↦ 0) V *ᵥ x) := by
  have hC : 0 ≤ sourcePairResidualError := le_max_left _ _
  have hres := source_pair_node_residual_lower b t A hA ht (by linarith) I hI i hi
    z y hz hρ hlo hhi u hu k hk
  have htwo := (source_pair_residual_time b t A (1 / 2) hA ht (by norm_num)
    (by linarith) I hI i hi).2
  norm_num only at htwo
  have hB := source_pair_brownian_lower t A hA ht I hI i
  dsimp only
  intro x
  apply pairObservation_compensated_lower (Fin.last (I - i)) _ _ hB.1
  · exact covariance_comm _ _
  · exact hB.2
  · intro a c
    have hr := hres ![a, c]
    rw [pairResidualMatrix_quadratic] at hr
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hr
    simp only [Fin.val_last, Bool.false_eq_true, ↓reduceIte]
    have hfactor : 1 ≤ (sourceLowerTime (sourceLowerRadius t) -
        sourceObservationTime t A I (I - i + 1)) / 2 := by linarith
    have hs := mul_le_mul_of_nonneg_right hfactor (add_nonneg (sq_nonneg a) (sq_nonneg c))
    have hs' : a ^ 2 + c ^ 2 ≤
        ((sourceLowerTime (sourceLowerRadius t) -
          sourceObservationTime t A I (I - i + 1)) / 2) * (a ^ 2 + c ^ 2) := by
      simpa only [one_mul] using hs
    exact hs'.trans hr

end SRWTightness
