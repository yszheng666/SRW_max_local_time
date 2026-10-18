import SRWTightness.SourceUpperRootEndpointRatio

namespace SRWTightness

/-- The actual target tilt has logarithmic-over-radius size, uniformly in the root block. -/
theorem source_upper_terminal_tilt_error (t s B : ℝ) (b : Site)
    (ht : 0 < t) (hB0 : 0 ≤ B) (hs : 0 ≤ s) (hslog : s ≤ Real.log t)
    (hT : t / 2 ≤ sourceUpperTotalDepth t) (hB : |sourceUpperTotalDepth t - t| ≤ B)
    (hk : sourceUpperBlockRoot t b < sourceUpperCoarseDepth t)
    (hklog : (sourceUpperBlockRoot t b : ℝ) ≤ Real.log t + 1)
    (hL : t / 2 ≤ (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ))
    (hθ0 : 0 ≤ sourceUpperSlope t s) (hθ : sourceUpperSlope t s ≤ 3) :
    |sourceUpperTarget t s /
      (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) - 2| ≤
      ((8 + 2 * Real.sqrt Real.pi) * Real.log t + 4 * B + 6) / t := by
  let L : ℝ := (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ)
  let k : ℝ := sourceUpperBlockRoot t b
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hN : (sourceUpperCoarseDepth t : ℝ) = L + k := by
    dsimp [L, k]
    rw [Nat.cast_sub hk.le]
    ring
  have hid : sourceUpperTarget t s / L - 2 =
      (sourceUpperSlope t s - 2) + sourceUpperSlope t s * k / L := by
    unfold sourceUpperTarget
    rw [hN]
    field_simp
    <;> ring
  have hcor : sourceUpperSlope t s * k / L ≤ 6 * (Real.log t + 1) / t := by
    calc
      _ ≤ (3 * k) / L := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hθ hk0) hL0.le
      _ ≤ (3 * k) / (t / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hL
      _ = 6 * k / t := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hklog (by norm_num : (0 : ℝ) ≤ 6)) ht.le
  change |sourceUpperTarget t s / L - 2| ≤ _
  rw [hid]
  calc
    _ ≤ |sourceUpperSlope t s - 2| + |sourceUpperSlope t s * k / L| := abs_add_le _ _
    _ = |sourceUpperSlope t s - 2| + sourceUpperSlope t s * k / L := by
      rw [abs_of_nonneg (by positivity : 0 ≤ sourceUpperSlope t s * k / L)]
    _ ≤ 2 * ((1 + Real.sqrt Real.pi) * Real.log t + 2 * B) / t +
        6 * (Real.log t + 1) / t :=
      add_le_add (source_upper_slope_error t s B ht hs hslog hT hB) hcor
    _ = _ := by ring

end SRWTightness
