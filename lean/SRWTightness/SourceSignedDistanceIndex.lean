import SRWTightness.SourceCommonPairDistance

namespace SRWTightness

/-- The manuscript distance index uses an integer floor and can be negative. -/
noncomputable def sourceSignedDistanceIndex (t ρ : ℝ) : ℤ :=
  ⌊Real.log (sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 / ρ)⌋

/-- Natural truncation always dominates the signed manuscript distance index. -/
theorem source_signed_distance_le_natural (t ρ : ℝ) :
    sourceSignedDistanceIndex t ρ ≤ (sourceCommonPairDistanceIndex t ρ : ℤ) := by
  unfold sourceSignedDistanceIndex sourceCommonPairDistanceIndex
  rw [← Int.floor_toNat]
  omega

/-- Every positive natural distance index equals the signed manuscript distance index. -/
theorem source_signed_distance_eq_natural (t ρ : ℝ)
    (h : 0 < sourceCommonPairDistanceIndex t ρ) :
    sourceSignedDistanceIndex t ρ = (sourceCommonPairDistanceIndex t ρ : ℤ) := by
  unfold sourceSignedDistanceIndex sourceCommonPairDistanceIndex at *
  rw [← Int.floor_toNat] at h ⊢
  omega

end SRWTightness
