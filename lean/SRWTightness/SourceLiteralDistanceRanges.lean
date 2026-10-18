import SRWTightness.SourceBoundedSignedDistance
import SRWTightness.SourceFixedPairSumBound

namespace SRWTightness

/-- The natural distance index is the nonnegative truncation of the literal integer floor. -/
theorem source_signed_distance_toNat (t ρ : ℝ) :
    (sourceSignedDistanceIndex t ρ).toNat = sourceCommonPairDistanceIndex t ρ := by
  unfold sourceSignedDistanceIndex sourceCommonPairDistanceIndex
  exact Int.floor_toNat _

/-- Positive early-distance intervals agree exactly in the signed and natural presentations. -/
theorem source_signed_early_range_iff (t ρ : ℝ) (a₀ L : ℕ) (ha₀ : 0 < a₀) :
    ((a₀ : ℤ) ≤ sourceSignedDistanceIndex t ρ ∧ sourceSignedDistanceIndex t ρ < (L : ℤ)) ↔
      (a₀ ≤ sourceCommonPairDistanceIndex t ρ ∧ sourceCommonPairDistanceIndex t ρ < L) := by
  have he := source_signed_distance_toNat t ρ
  omega

/-- On a positive early range the literal integer is retained without truncation. -/
theorem source_signed_early_index_eq (t ρ : ℝ) (a₀ : ℕ) (ha₀ : 0 < a₀)
    (ha : (a₀ : ℤ) ≤ sourceSignedDistanceIndex t ρ) :
    sourceSignedDistanceIndex t ρ = (sourceCommonPairDistanceIndex t ρ : ℤ) := by
  have he := source_signed_distance_toNat t ρ
  omega

/-- The bounded-distance pair set defined with the literal floor includes every negative index. -/
theorem source_literal_fixed_pairs_eq (t : ℝ) (a₀ : ℕ) :
    ((sourceCandidateAnnulus (Real.exp t)).product (sourceCandidateAnnulus (Real.exp t))).filter
      (fun p ↦ p.1 ≠ p.2 ∧
        sourceSignedDistanceIndex t (Real.sqrt (normSq (p.2 - p.1))) ≤ (a₀ : ℤ)) =
      sourceFixedDistancePairs t a₀ := by
  classical
  unfold sourceFixedDistancePairs
  apply Finset.filter_congr
  intro p hp
  rw [source_bounded_signed_distance_iff]

end SRWTightness
