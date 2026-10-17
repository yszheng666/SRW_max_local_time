import SRWTightness.SourceSignedDistanceIndex

namespace SRWTightness

/-- A nonnegative fixed cutoff selects exactly the same distances before or after natural
truncation, so the bounded-index estimates include all negative manuscript indices. -/
theorem source_bounded_signed_distance_iff (t ρ : ℝ) (a₀ : ℕ) :
    sourceSignedDistanceIndex t ρ ≤ (a₀ : ℤ) ↔ sourceCommonPairDistanceIndex t ρ ≤ a₀ := by
  unfold sourceSignedDistanceIndex sourceCommonPairDistanceIndex
  rw [← Int.floor_toNat]
  omega

end SRWTightness
