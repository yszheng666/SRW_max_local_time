import SRWTightness.SourceDeficitBand

open Filter
namespace SRWTightness

/-- The manuscript cap on the original root count at the early comparison level. -/
noncomputable def sourceEarlyRootCap (t : ℝ) (ν : ℕ) : ℕ :=
  ⌊(4 + sourceBarrierSlope t * (ν : ℝ)) ^ 2 / 2⌋₊

/-- The source barrier height gives its exact integer root cap. -/
theorem source_early_root_cap_of_height (t : ℝ) (ν k : ℕ)
    (hθ : 0 ≤ sourceBarrierSlope t)
    (hk : Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * (ν : ℝ)) :
    k ≤ sourceEarlyRootCap t ν := by
  unfold sourceEarlyRootCap
  apply (Nat.le_floor_iff (by positivity)).mpr
  have hnon := Real.sqrt_nonneg (2 * (k : ℝ))
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * (k : ℝ) by positivity)
  have hheight : 0 ≤ 4 + sourceBarrierSlope t * (ν : ℝ) := by positivity
  nlinarith

/-- The actual integer cap is uniformly at most eight times the squared early level. -/
theorem source_early_root_cap_quadratic :
    ∀ᶠ t : ℝ in atTop, ∀ ν : ℕ,
      (sourceEarlyRootCap t ν : ℝ) ≤ 8 * ((ν : ℝ) + 1) ^ 2 := by
  filter_upwards [source_deficit_large_conditions] with t ht
  intro ν
  have hθ := sourceBarrierSlope_bounds t ht.1 ht.2.1
  have hfloor := Nat.floor_le (show 0 ≤ (4 + sourceBarrierSlope t * (ν : ℝ)) ^ 2 / 2 by positivity)
  have hν : (0 : ℝ) ≤ ν := Nat.cast_nonneg _
  have hθ0 := hθ.1
  have hh : 0 ≤ 4 + sourceBarrierSlope t * (ν : ℝ) := by positivity
  have hu := mul_le_mul_of_nonneg_right hθ.2 hν
  change (⌊(4 + sourceBarrierSlope t * (ν : ℝ)) ^ 2 / 2⌋₊ : ℝ) ≤ _
  nlinarith

end SRWTightness
