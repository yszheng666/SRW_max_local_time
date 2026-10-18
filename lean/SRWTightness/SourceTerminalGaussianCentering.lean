import SRWTightness.SourceTerminalBridgeEvent
import SRWTightness.SourceGaussianGridPath
import SRWTightness.GaussianGridTerminalEventLaw

namespace SRWTightness

/-- The mean translation identifies all source terminal constraints pointwise. -/
theorem sourceTerminalBridgeEvent_gaussian_centering (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (At q aStar d γ : ℝ) (x : Fin ((I + 1) + 1) → ℝ)
    (ω : ℕ → GaussianCoefficientSpace) :
    ((fun i ↦ 2 * sourceObservationTime t A I (i.val + 1) + x i), ω) ∈
        sourceTerminalBridgeEvent t A I At q aStar d γ ↔
      (x, ω) ∈ gaussianGridTerminalEvent (sourceObservationTime t A I) (I + 1)
        (q - aStar - 1) (q - aStar) At (sourceObservationTime t A I (I + 2)) q d γ := by
  have hn := sourceBridgedPath_node t A hA ht I hI
    (fun i ↦ 2 * sourceObservationTime t A I (i.val + 1) + x i) ω (Fin.last I)
  rw [sourceBridgedPath_gaussian_centering] at hn
  have hend : gaussianGridPath (sourceObservationTime t A I) (I + 1) (x, ω)
      (sourceObservationTime t A I (I + 1)) = x ⟨I, by omega⟩ := by
    have hi : (Fin.last I).castSucc = (⟨I, by omega⟩ : Fin ((I + 1) + 1)) := by
      apply Fin.ext
      rfl
    simpa only [Fin.val_last, add_sub_cancel_left, hi] using hn
  simp only [sourceTerminalBridgeEvent, sourceBridgedBarrierEvent,
    gaussianGridTerminalEvent, gaussianGridEndpointCurveEvent, Set.mem_setOf_eq,
    Set.mem_Icc, sourceBridgedPath_gaussian_centering, hend, Fin.val_last]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, h5⟩, h1, h2⟩
  · rintro ⟨⟨⟨h3, h4⟩, h5⟩, h1, h2⟩
    exact ⟨h1, h2, by linarith, by linarith, h5⟩

end SRWTightness
