import SRWTightness.ActualIntervalBridge
import SRWTightness.SourceGaussianComparison
import SRWTightness.SourceObservationTime

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual source covariance has a uniform upper comparison for every auxiliary-path event. -/
theorem source_gaussian_event_upper (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I)
    (E : Set ((Fin ((I + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace))) :
    let K := brownianTimeMatrix (sourceObservationTime t A I) ((I + 1) + 1)
    let e := geometricDiskPointError b A (Real.exp 1 * sourceLowerRadius t + 14)
      diskEnergyGapRatio (2 / Real.pi) (I + 1)
    ((gaussianCoordinateLaw (K - Matrix.diagonal e)).prod (independentBridgeLaw ℕ)).real E ≤
      Real.exp (4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi))) *
        ((gaussianCoordinateLaw K).prod (independentBridgeLaw ℕ)).real E := by
  obtain ⟨J, hJ, hc⟩ := source_gaussian_comparison (independentBridgeLaw ℕ) b t A hA ht
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  dsimp only at hc ⊢
  let K := brownianTimeMatrix (sourceObservationTime t A I) ((I + 1) + 1)
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hle := hc.2.1 E
  have hh := ENNReal.toReal_mono (by
    change (ENNReal.ofReal (Real.exp (4 * diskEquilibriumWeightConstant /
      (A * (2 / Real.pi)))) •
      ((gaussianCoordinateLaw K).prod (independentBridgeLaw ℕ))) E ≠ ⊤
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hle
  change _ ≤ _ at hh
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hh
  exact hh

end SRWTightness
