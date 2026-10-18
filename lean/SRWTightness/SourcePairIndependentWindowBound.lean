import SRWTightness.SourcePairBrownianWindowScale
import SRWTightness.GaussianResidualWindowProduct
import SRWTightness.FiniteGaussianPrefixMeasurable

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Combining the Brownian prefix with two residual unit windows gives the pair prefactor. -/
theorem source_pair_independent_window_bound (hKernel : FiniteGaussianBridgeKernelInput)
    (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (q f e : ℝ) (l : ℕ) (hq : 0 < q) (hf : 0 ≤ f) (he : 0 ≤ e) (heu : e ≤ 1 / 2)
    (hd : 0 < sourceLowerTime (sourceLowerRadius t))
    (hv : sourceLowerTime (sourceLowerRadius t) / 2 ≤
      sourceObservationTime t A I (I - i + 1))
    (hqu : q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.PosDef) (C h : ℝ) (hC : 0 ≤ C) (hh : 0 < h)
    (hbound : ∀ x, (gaussianCovarianceDensity R x).toReal ≤ C / h)
    (a : ((Fin (I - i + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) → Fin 2 → ℝ)
    (ha : Measurable a) :
    let μ := (gaussianCoordinateLaw (fun j k : Fin (I - i + 1) ↦
      min (sourceObservationTime t A I (j.val + 1))
        (sourceObservationTime t A I (k.val + 1)))).prod (independentBridgeLaw ℕ)
    let s := finiteGaussianPrefixWindow (sourceObservationTime t A I) (I - i + 1) (I + 1)
      (Fin.last (I - i)) q (q - f - l - 1 - 2 * e) (q - f - l - 2 * e)
    (μ.prod (gaussianCoordinateLaw R)).real
      {p | p.1 ∈ s ∧ ∀ j, a p.1 j ≤ p.2 j ∧ p.2 j < a p.1 j + 1} ≤
      16 * C * (f + l + 1) /
        (sourceLowerTime (sourceLowerRadius t) * h) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure
    (fun j k : Fin (I - i + 1) ↦ min (sourceObservationTime t A I (j.val + 1))
      (sourceObservationTime t A I (k.val + 1)))
  dsimp only
  have hb := source_pair_brownian_window_scaled hKernel t A I i hA ht hI
    q f e l hq hf he heu hd hv hqu
  have hp := gaussian_residual_window_product
    ((gaussianCoordinateLaw (fun j k : Fin (I - i + 1) ↦
      min (sourceObservationTime t A I (j.val + 1))
        (sourceObservationTime t A I (k.val + 1)))).prod (independentBridgeLaw ℕ))
    R hR (C / h) (div_nonneg hC hh.le) hbound _
    (finiteGaussianPrefixWindow_measurable (sourceObservationTime t A I)
      (I - i + 1) (I + 1) (Fin.last (I - i)) q
      (q - f - l - 1 - 2 * e) (q - f - l - 2 * e)) a ha
  exact hp.trans ((mul_le_mul_of_nonneg_left hb (div_nonneg hC hh.le)).trans_eq (by ring))

end SRWTightness
