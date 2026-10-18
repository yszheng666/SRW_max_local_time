import SRWTightness.SourcePairNodeResidual
import SRWTightness.SourcePairResidualDensity

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The Gaussian density for the actual node residual is bounded by a constant over its time deficit. -/
theorem source_pair_node_residual_density_upper (b : Site) (t A : ℝ)
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
      (gaussianCovarianceDensity
        (pairResidualMatrix (covariance (F z) (F z) μ) (covariance (F y) (F y) μ)
          (covariance (F z) (F y) μ) (sourceObservationTime t A I (I - i + 1))) x).toReal ≤
        2 * ((Real.sqrt (2 * Real.pi))⁻¹ ^ 2) /
          (sourceLowerTime m - sourceObservationTime t A I (I - i + 1)) := by
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
  have hh := source_pair_residual_density_upper b (sourceLowerRadius t) 14
    (A * diskEnergyGapRatio ^ i) (4 * diskEnergyGapRatio)
    (by linarith) (by norm_num) (by linarith) hma _ hMD z y hz hρ hlo hhi
    u hu hcap k hk hr.1 (by linarith [hr.2])
  dsimp only
  rw [source_observation_time_at_radius b t A I i hi]
  exact hh

end SRWTightness
