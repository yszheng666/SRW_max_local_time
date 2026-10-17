import SRWTightness.SourcePairNodeResidual
import SRWTightness.PairResidualLower

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The actual retained-node residual has a uniform quantitative lower bound. -/
theorem source_pair_node_residual_lower (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : 4 * sourcePairResidualError + 1 + sourceEquilibriumTimeError +
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
    ∀ x : Fin 2 → ℝ,
      ((sourceLowerTime m - sourceObservationTime t A I (I - i + 1)) / 2) *
        (∑ j, x j ^ 2) ≤ x ⬝ᵥ
          (pairResidualMatrix (covariance (F z) (F z) μ) (covariance (F y) (F y) μ)
            (covariance (F z) (F y) μ) (sourceObservationTime t A I (I - i + 1)) *ᵥ x) := by
  obtain ⟨ha, hma, hMD, hKM, hcap⟩ :=
    source_pair_observation_geometry b t A hA ht I hI i hi
  have hC : 0 ≤ sourcePairResidualError := le_max_left _ _
  have hm := (sourceScaleThreshold_conditions t A
    (diskGaussianMinimumRadius_ge_four.trans
      (diskPointGaussianMinimumRadius_ge_base.trans hA))
    ((le_max_left _ _).trans ht)).2.2.1
  have hr := source_pair_residual_time b t A sourcePairResidualError hA ht hC
    (by linarith) I hI i hi
  rw [source_observation_time_at_radius b t A I i hi] at hr
  have hbound : max sourcePairVarianceError
      (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 +
        Real.log (4 * diskEnergyGapRatio)) ≤ sourcePairResidualError := le_max_right _ _
  obtain ⟨hzv, hyv, hcross⟩ := source_pair_covariance_bounds b (sourceLowerRadius t) 14
    (A * diskEnergyGapRatio ^ i) (4 * diskEnergyGapRatio)
    (by linarith) (by norm_num) (by linarith) hma _ hMD z y hz hρ hlo hhi u hu hcap k hk
  dsimp only
  intro x
  rw [source_observation_time_at_radius b t A I i hi]
  exact pairResidualMatrix_lower _ _ _ _ _ sourcePairResidualError hC hr.2
    (hzv.trans ((le_max_left _ _).trans hbound))
    (hyv.trans ((le_max_left _ _).trans hbound))
    (hcross.trans ((le_max_right _ _).trans hbound)) x

end SRWTightness
