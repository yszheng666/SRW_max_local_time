import SRWTightness.SourceSignedDistanceIndex

namespace SRWTightness

/-- The source common endpoint is an integer difference, including negative early levels. -/
noncomputable def sourceSignedCommonPairLevel (t ρ : ℝ) : ℤ :=
  sourceSignedDistanceIndex t ρ - (⌈10 * Real.log t⌉ + 5)

/-- The source logarithmic gap agrees with its literal integer ceiling for t at least one. -/
theorem source_common_pair_gap_integer (t : ℝ) (ht : 1 ≤ t) :
    (sourceCommonPairGap t : ℤ) = ⌈10 * Real.log t⌉ + 5 := by
  simp only [sourceCommonPairGap, Nat.cast_add, Nat.cast_ofNat]
  rw [Int.natCast_ceil_eq_ceil (mul_nonneg (by norm_num) (Real.log_nonneg ht))]

/-- The nonnegative common level agrees with the signed source level whenever the gap fits. -/
theorem source_common_pair_level_signed (t ρ : ℝ) (ht : 1 ≤ t)
    (hgap : sourceCommonPairGap t ≤ sourceCommonPairDistanceIndex t ρ) :
    (sourceCommonPairLevel t ρ : ℤ) = sourceSignedCommonPairLevel t ρ := by
  have hp : 0 < sourceCommonPairDistanceIndex t ρ := by
    have hg : 5 ≤ sourceCommonPairGap t := by unfold sourceCommonPairGap; omega
    omega
  unfold sourceSignedCommonPairLevel sourceCommonPairLevel
  rw [Nat.cast_sub hgap, source_signed_distance_eq_natural t ρ hp,
    source_common_pair_gap_integer t ht]

/-- The literal signed endpoint plus the literal gap equals the literal distance floor. -/
theorem source_common_pair_signed_level_formula (t ρ : ℝ) :
    sourceSignedCommonPairLevel t ρ + (⌈10 * Real.log t⌉ + 5) =
      sourceSignedDistanceIndex t ρ := by
  unfold sourceSignedCommonPairLevel
  omega

/-- A nonnegative level satisfying the literal signed formula has the exact natural index sum. -/
theorem source_common_signed_level_index_sum (t ρ : ℝ) (ht : 1 ≤ t) (j : ℕ)
    (hj : (j : ℤ) = sourceSignedCommonPairLevel t ρ) :
    j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ := by
  have hg := source_common_pair_gap_integer t ht
  have he : (j : ℤ) + (sourceCommonPairGap t : ℤ) = sourceSignedDistanceIndex t ρ := by
    unfold sourceSignedCommonPairLevel at hj
    omega
  have hle := source_signed_distance_le_natural t ρ
  have hgap : 5 ≤ sourceCommonPairGap t := by unfold sourceCommonPairGap; omega
  have hp : 0 < sourceCommonPairDistanceIndex t ρ := by omega
  rw [source_signed_distance_eq_natural t ρ hp] at he
  exact_mod_cast he

end SRWTightness
