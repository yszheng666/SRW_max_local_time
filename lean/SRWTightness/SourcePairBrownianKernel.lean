import SRWTightness.SourcePairFiniteGaussianPath

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The standard killed Brownian kernel applies to the actual retained source time grid. -/
theorem source_pair_brownian_kernel (hKernel : FiniteGaussianBridgeKernelInput)
    (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (q a b : ℝ) (hq : 0 < q) (hab : a ≤ b) (hbq : b ≤ q) :
    ((gaussianCoordinateLaw (fun j l : Fin (I - i + 1) ↦
      min (sourceObservationTime t A I (j.val + 1))
        (sourceObservationTime t A I (l.val + 1)))).prod (independentBridgeLaw ℕ)).real
      (finiteGaussianPrefixWindow (sourceObservationTime t A I) (I - i + 1) (I + 1)
        (Fin.last (I - i)) q a b) =
      ∫ s in Set.Icc a b, gaussianPDFReal 0 (sourceObservationTime t A I (I - i + 1)).toNNReal s *
        (1 - Real.exp (-(2 * q * (q - s) / sourceObservationTime t A I (I - i + 1)))) := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  exact hKernel (sourceObservationTime t A I) (I - i + 1) (I + 1) (Fin.last (I - i))
    (by simp) (by omega) (sourceObservationTime_zero t A I)
    (fun j hj ↦ by linarith [hg j (by omega)]) q a b hq hab hbq

end SRWTightness
