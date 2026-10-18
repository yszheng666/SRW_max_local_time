import SRWTightness.SourceCoarseExponentExpansion

namespace SRWTightness

/-- Bounded exponent errors and comparable time scales give the normalized window weight. -/
theorem coarse_terminal_weight_bounds (t d N q K X R : ℝ)
    (ht : 0 < t) (hd : 0 < d) (hq : 0 ≤ q)
    (hNl : t / 4 ≤ N) (hNu : N ≤ 2 * t)
    (hX : |X - (2 * t - 2 * d - 2 * Real.log t)| ≤ K) (hR : |R| ≤ 1) :
    (Real.exp (-K - 1) / 4) * (Real.exp (-2 * t) * (1 + q) / d) ≤
      ((1 + q) / N ^ 2) * (Real.exp (-X - 2 * d) * Real.exp R) / d ∧
    ((1 + q) / N ^ 2) * (Real.exp (-X - 2 * d) * Real.exp R) / d ≤
      (16 * Real.exp (K + 1)) * (Real.exp (-2 * t) * (1 + q) / d) := by
  have hN : 0 < N := by linarith
  let E := -X + 2 * t - 2 * d - 2 * Real.log t + R
  have hEl : -K - 1 ≤ E := by
    dsimp [E]
    linarith [(abs_le.mp hX).2, (abs_le.mp hR).1]
  have hEu : E ≤ K + 1 := by
    dsimp [E]
    linarith [(abs_le.mp hX).1, (abs_le.mp hR).2]
  have hexp : Real.exp (-X - 2 * d) * Real.exp R =
      Real.exp (-2 * t) * t ^ 2 * Real.exp E := by
    have hlog : t ^ 2 = Real.exp (Real.log t + Real.log t) := by
      rw [Real.exp_add, Real.exp_log ht]
      ring
    rw [hlog, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [E]
    ring
  have hratioL : (1 / 4 : ℝ) ≤ t ^ 2 / N ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < N ^ 2)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 2 * t - N by linarith)
      (show 0 ≤ 2 * t + N by linarith)]
  have hratioU : t ^ 2 / N ^ 2 ≤ 16 := by
    apply (div_le_iff₀ (by positivity : 0 < N ^ 2)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 4 * N - t by linarith)
      (show 0 ≤ 4 * N + t by linarith)]
  have hfL : Real.exp (-K - 1) / 4 ≤ (t ^ 2 / N ^ 2) * Real.exp E := by
    have hh := mul_le_mul hratioL (Real.exp_le_exp.mpr hEl)
      (Real.exp_nonneg _) (by positivity : 0 ≤ t ^ 2 / N ^ 2)
    nlinarith only [hh]
  have hfU : (t ^ 2 / N ^ 2) * Real.exp E ≤ 16 * Real.exp (K + 1) :=
    mul_le_mul hratioU (Real.exp_le_exp.mpr hEu) (Real.exp_nonneg _) (by norm_num)
  have hweight : 0 ≤ Real.exp (-2 * t) * (1 + q) / d := by positivity
  rw [hexp]
  constructor
  · calc
      _ ≤ (t ^ 2 / N ^ 2 * Real.exp E) * (Real.exp (-2 * t) * (1 + q) / d) :=
        mul_le_mul_of_nonneg_right hfL hweight
      _ = _ := by ring
  · calc
      _ = (t ^ 2 / N ^ 2 * Real.exp E) * (Real.exp (-2 * t) * (1 + q) / d) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfU hweight

end SRWTightness
