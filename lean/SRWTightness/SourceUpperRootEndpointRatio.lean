import SRWTightness.SourceUpperRootSlopeError

namespace SRWTightness

/-- The actual branching endpoint ratio is controlled by the explicit vanishing slope error. -/
theorem source_upper_root_endpoint_ratio (t s B : ℝ) (b : Site)
    (ht : 0 < t) (hlog : 1 ≤ Real.log t) (hB0 : 0 ≤ B)
    (hs : 0 ≤ s) (hslog : s ≤ Real.log t)
    (hT : t / 2 ≤ sourceUpperTotalDepth t) (hB : |sourceUpperTotalDepth t - t| ≤ B)
    (hd : 1 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hk : sourceUpperBlockRoot t b < sourceUpperCoarseDepth t)
    (hklog : (sourceUpperBlockRoot t b : ℝ) ≤ Real.log t + 1)
    (hL : t / 2 ≤ (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ))
    (hθ : sourceUpperSlope t s ≤ 3) :
    sourceUpperBranchingEnd t s /
      (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) ≤
        2 + sourceUpperRootSlopeError t B := by
  let L : ℝ := (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ)
  let E := 4 * Real.log t + 7 + 2 * upperTerminalDepth (sourceUpperLogRadius t)
  let ε := 2 * ((1 + Real.sqrt Real.pi) * Real.log t + 2 * B) / t
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hE : 0 ≤ E := by dsimp [E]; linarith
  have hε : sourceUpperSlope t s ≤ 2 + ε := by
    have hh := (abs_le.mp (source_upper_slope_error t s B ht hs hslog hT hB)).2
    dsimp [ε]
    linarith
  have hroot := Real.rpow_le_self_of_one_le hd (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hN : (sourceUpperCoarseDepth t : ℝ) = L + sourceUpperBlockRoot t b := by
    dsimp [L]
    rw [Nat.cast_sub hk.le]
    ring
  have he : sourceUpperBranchingEnd t s ≤ sourceUpperSlope t s * L + E := by
    unfold sourceUpperBranchingEnd sourceUpperTarget
    rw [hN]
    have hm := mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg (sourceUpperBlockRoot t b))
    dsimp [E]
    nlinarith
  have hquot : E / L ≤ 2 * E / t := by
    calc
      _ ≤ E / (t / 2) := div_le_div_of_nonneg_left hE (by positivity) hL
      _ = _ := by ring
  have hid : ε + 2 * E / t = sourceUpperRootSlopeError t B := by
    dsimp [ε, E, sourceUpperRootSlopeError]
    ring
  calc
    _ ≤ (sourceUpperSlope t s * L + E) / L := div_le_div_of_nonneg_right he hL0.le
    _ = sourceUpperSlope t s + E / L := by rw [add_div, mul_div_cancel_right₀ _ hL0.ne']
    _ ≤ (2 + ε) + 2 * E / t := add_le_add hε hquot
    _ = _ := by rw [add_assoc, hid]

end SRWTightness
