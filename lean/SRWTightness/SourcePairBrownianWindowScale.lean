import SRWTightness.SourcePairBrownianWindowBound
import SRWTightness.GaussianReflectionKernelScale

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual late-time Brownian endpoint window supplies the inverse source-time factor. -/
theorem source_pair_brownian_window_scaled (hKernel : FiniteGaussianBridgeKernelInput)
    (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (q f e : ℝ) (l : ℕ) (hq : 0 < q) (hf : 0 ≤ f) (he : 0 ≤ e) (heu : e ≤ 1 / 2)
    (hd : 0 < sourceLowerTime (sourceLowerRadius t))
    (hv : sourceLowerTime (sourceLowerRadius t) / 2 ≤
      sourceObservationTime t A I (I - i + 1))
    (hqu : q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) :
    ((gaussianCoordinateLaw (fun j k : Fin (I - i + 1) ↦
      min (sourceObservationTime t A I (j.val + 1))
        (sourceObservationTime t A I (k.val + 1)))).prod (independentBridgeLaw ℕ)).real
      (finiteGaussianPrefixWindow (sourceObservationTime t A I) (I - i + 1) (I + 1)
        (Fin.last (I - i)) q (q - f - l - 1 - 2 * e) (q - f - l - 2 * e)) ≤
      16 * (f + l + 1) / sourceLowerTime (sourceLowerRadius t) := by
  exact (source_pair_brownian_window_bound hKernel t A I i hA ht hI
    q f e l hq hf he).trans
    (gaussian_reflection_kernel_scale _ _ q f e l hd hv hq.le hqu hf he heu)

end SRWTightness
