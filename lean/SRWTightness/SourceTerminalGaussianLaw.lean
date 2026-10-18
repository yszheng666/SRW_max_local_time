import SRWTightness.SourceTerminalGaussianCentering
import SRWTightness.GaussianTranslation

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual source terminal event under the K-Gaussian mean law has the exact bridge product probability. -/
theorem sourceTerminalBridgeEvent_gaussian_probability
    (hReconstruct : BrownianBridgeReconstructionInput) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (At q aStar d γ : ℝ) :
    let T := sourceObservationTime t A I
    let m := fun i : Fin ((I + 1) + 1) ↦ 2 * T (i.val + 1)
    ((gaussianMeanCoordinateLaw m (brownianTimeMatrix T ((I + 1) + 1))).prod
      (independentBridgeLaw ℕ)).real (sourceTerminalBridgeEvent t A I At q aStar d γ) =
      (((gaussianReal 0 (T (I + 1)).toNNReal).prod gaussianCoefficientLaw).prod
        (gaussianReal 0 (T (I + 2) - T (I + 1)).toNNReal)).real
        (terminalBridgeProductEvent (T (I + 1)) (q - aStar - 1) (q - aStar)
          At (T (I + 2)) q d γ) := by
  dsimp only
  rw [gaussianMeanCoordinateLaw_prod_real _ _ _ _
    (sourceTerminalBridgeEvent_measurable _ _ _ _ _ _ _ _)]
  have he : (fun p : (Fin ((I + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦
      ((fun i ↦ 2 * sourceObservationTime t A I (i.val + 1)) + p.1, p.2)) ⁻¹'
        sourceTerminalBridgeEvent t A I At q aStar d γ =
      gaussianGridTerminalEvent (sourceObservationTime t A I) (I + 1)
        (q - aStar - 1) (q - aStar) At (sourceObservationTime t A I (I + 2)) q d γ := by
    ext p
    exact sourceTerminalBridgeEvent_gaussian_centering t A hA ht I hI At q aStar d γ p.1 p.2
  rw [he]
  exact gaussianGrid_terminal_event_probability hReconstruct _ _ (by omega)
    (sourceObservationTime_zero t A I) (sourceObservationTime_gaps t A hA ht I hI)
    _ _ _ _ _ _ _

end SRWTightness
