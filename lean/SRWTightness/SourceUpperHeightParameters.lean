import SRWTightness.SourceUpperMarkParameters

namespace SRWTightness

/-- The complete literal height, slope, target and integer cutoff of source (4.4). -/
theorem source_upper_height_parameters (R s : ℝ) :
    sourceUpperHeight (Real.log R) s =
      Real.sqrt Real.pi * (diskCenter R + s) ∧
    sourceUpperHeight (Real.log R) s =
      2 * Real.log R - Real.log (Real.log R) + Real.sqrt Real.pi * s ∧
    sourceUpperSlope (Real.log R) s =
      sourceUpperHeight (Real.log R) s / sourceUpperTotalDepth (Real.log R) ∧
    sourceUpperTarget (Real.log R) s =
      sourceUpperSlope (Real.log R) s * (sourceUpperCoarseDepth (Real.log R) : ℝ) ∧
    sourceUpperVisitCutoff (Real.log R) s = Nat.ceil ((diskCenter R + s) ^ 2) := by
  refine ⟨?_, rfl, rfl, rfl, sourceUpperVisitCutoff_at_radius R s⟩
  rw [sourceUpperHeight_at_radius]
  exact (mul_div_cancel₀ _ (Real.sqrt_pos.mpr Real.pi_pos).ne').symm

end SRWTightness
