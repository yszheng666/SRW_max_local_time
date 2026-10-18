import SRWTightness.SourcePairBrownianKernel
import SRWTightness.GaussianReflectionKernelBound

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The source deficit window has an explicit killed-Brownian probability upper bound. -/
theorem source_pair_brownian_window_bound (hKernel : FiniteGaussianBridgeKernelInput)
    (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (q f e : ℝ) (l : ℕ) (hq : 0 < q) (hf : 0 ≤ f) (he : 0 ≤ e) :
    let v := sourceObservationTime t A I (I - i + 1)
    ((gaussianCoordinateLaw (fun j k : Fin (I - i + 1) ↦
      min (sourceObservationTime t A I (j.val + 1))
        (sourceObservationTime t A I (k.val + 1)))).prod (independentBridgeLaw ℕ)).real
      (finiteGaussianPrefixWindow (sourceObservationTime t A I) (I - i + 1) (I + 1)
        (Fin.last (I - i)) q (q - f - l - 1 - 2 * e) (q - f - l - 2 * e)) ≤
      (Real.sqrt (2 * Real.pi * v))⁻¹ * (2 * q * (f + l + 1 + 2 * e) / v) := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hfirst := hg 0 (by omega)
  rw [sourceObservationTime_zero] at hfirst
  have hmono := timeGridTime_mono (sourceObservationTime t A I) (I + 1)
    (fun j hj ↦ by linarith [hg j (by omega)])
    (show 1 ≤ I - i + 1 by omega) (show I - i + 1 ≤ I + 1 by omega)
  have hv : 0 < sourceObservationTime t A I (I - i + 1) := by
    norm_num only at hfirst
    linarith
  have hab : q - f - (l : ℝ) - 1 - 2 * e ≤ q - f - l - 2 * e := by linarith
  have hbq : q - f - (l : ℝ) - 2 * e ≤ q := by
    have hl : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
    linarith
  dsimp only
  rw [source_pair_brownian_kernel hKernel t A I i hA ht hI _ _ _ hq hab hbq]
  have hh := gaussian_reflection_kernel_interval_bound
    (sourceObservationTime t A I (I - i + 1)) q
    (q - f - l - 1 - 2 * e) (q - f - l - 2 * e) hv hq.le hab hbq
  convert hh using 1 <;> ring

end SRWTightness
