import SRWTightness.SourceEarlyRootCap

namespace SRWTightness

/-- The original integer root cap supplies exactly the starting-height condition required by
the source continuation bound. -/
theorem source_early_root_height_of_cap (t : ℝ) (ν k : ℕ)
    (hθ : 0 ≤ sourceBarrierSlope t) (hk : k ≤ sourceEarlyRootCap t ν) :
    Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * (ν : ℝ) := by
  have hkR : (k : ℝ) ≤ (sourceEarlyRootCap t ν : ℝ) := Nat.cast_le.mpr hk
  have hf := Nat.floor_le
    (show 0 ≤ (4 + sourceBarrierSlope t * (ν : ℝ)) ^ 2 / 2 by positivity)
  change (sourceEarlyRootCap t ν : ℝ) ≤ _ at hf
  apply (Real.sqrt_le_left (show 0 ≤ 4 + sourceBarrierSlope t * (ν : ℝ) by positivity)).mpr
  linarith

end SRWTightness
