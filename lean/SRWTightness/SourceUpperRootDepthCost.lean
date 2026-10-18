import SRWTightness.SourceUpperRootEndpointRatio

namespace SRWTightness

/-- The reduced forest depth contributes exactly the extra quadratic cost in source (4.31). -/
theorem source_upper_root_depth_cost (t s : ℝ) (k : ℕ)
    (hk : k < sourceUpperCoarseDepth t) :
    sourceUpperTarget t s ^ 2 / (2 * (sourceUpperCoarseDepth t - k : ℕ)) -
        sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t) =
      sourceUpperSlope t s ^ 2 * sourceUpperCoarseDepth t * k /
        (2 * (sourceUpperCoarseDepth t - k : ℕ)) := by
  have hN : (sourceUpperCoarseDepth t : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hk)
  have hL : (sourceUpperCoarseDepth t : ℝ) - k ≠ 0 := by
    have h : (k : ℝ) < sourceUpperCoarseDepth t := by exact_mod_cast hk
    linarith
  unfold sourceUpperTarget
  rw [Nat.cast_sub hk.le]
  field_simp [hN, hL] <;> ring

/-- A source slope at least three halves gives exponential decay in every root level. -/
theorem source_upper_root_depth_cost_lower (t s : ℝ) (k : ℕ)
    (hk : k < sourceUpperCoarseDepth t) (hθ : 3 / 2 ≤ sourceUpperSlope t s) :
    9 * (k : ℝ) / 8 ≤
      sourceUpperTarget t s ^ 2 / (2 * (sourceUpperCoarseDepth t - k : ℕ)) -
        sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t) := by
  rw [source_upper_root_depth_cost t s k hk]
  have hL : (0 : ℝ) < (sourceUpperCoarseDepth t - k : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hk
  have hLN : (sourceUpperCoarseDepth t - k : ℕ) ≤ (sourceUpperCoarseDepth t : ℝ) := by
    exact_mod_cast Nat.sub_le (sourceUpperCoarseDepth t) k
  have hs : (9 / 4 : ℝ) ≤ sourceUpperSlope t s ^ 2 := by nlinarith
  have hh := mul_le_mul hs hLN (by positivity : (0 : ℝ) ≤ (sourceUpperCoarseDepth t - k : ℕ))
    (by positivity : 0 ≤ sourceUpperSlope t s ^ 2)
  have hm := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) k)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (sourceUpperCoarseDepth t - k : ℕ))).mpr
  nlinarith

end SRWTightness
