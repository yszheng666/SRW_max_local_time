import SRWTightness.SourceDeficitBand
import SRWTightness.SourceCommonPairEndpoint
import SRWTightness.SourceUpperVisitThreshold

namespace SRWTightness

/-- The literal lower height, slope, root, cutoff and implemented barrier width of (5.3). -/
theorem source_lower_height_parameters (R : ℝ) (j : ℕ) :
    sourceTerminalHeight (Real.log R) = 2 * Real.log R - Real.log (Real.log R) ∧
    sourceTerminalHeight (Real.log R) = Real.sqrt Real.pi * diskCenter R ∧
    sourceBarrierSlope (Real.log R) =
      sourceTerminalHeight (Real.log R) / sourceTotalTime (Real.log R) ∧
    sourceTerminalRoot (Real.log R) 0 =
      sourceBarrierSlope (Real.log R) * (sourceCoarseGeneration (Real.log R) : ℝ) ∧
    sourceTerminalVisitCutoff (Real.log R) = Nat.ceil (diskCenter R ^ 2) ∧
    4 + sourceBarrierSlope (Real.log R) * j - sourceCommonPairEndpoint (Real.log R) j =
      (min (j : ℝ) (sourceTotalTime (Real.log R) - j)) ^ (2 / 5 : ℝ) := by
  refine ⟨rfl, ?_, rfl, ?_, sourceTerminalVisitCutoff_at_radius R, ?_⟩
  · have he := sourceUpperHeight_at_radius R 0
    simp only [add_zero] at he
    have hs : sourceUpperHeight (Real.log R) 0 = sourceTerminalHeight (Real.log R) := by
      simp [sourceUpperHeight, sourceTerminalHeight]
    rw [hs] at he
    rw [he]
    exact (mul_div_cancel₀ _ (Real.sqrt_pos.mpr Real.pi_pos).ne').symm
  · simp [sourceTerminalRoot]
  · unfold sourceCommonPairEndpoint
    ring

end SRWTightness
