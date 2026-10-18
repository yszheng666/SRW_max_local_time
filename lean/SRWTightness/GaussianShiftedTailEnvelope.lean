import SRWTightness.SourceUpperSmallHeightTail

namespace SRWTightness

/-- Bounded centering shifts and a twofold logarithmic-scale change preserve a quadratic tail. -/
theorem gaussian_shifted_tail_envelope (D c a z h H : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hh : 1 ≤ h) (hH : 0 < H) (hHu : H ≤ 2 * h) (hz : 1 ≤ z - a) :
    D * (1 + (z - a)) * Real.exp (-2 * (z - a) - c * (z - a) ^ 2 / H) ≤
      (D * Real.exp (2 * a + c * a ^ 2 / 2)) * (1 + z) *
        Real.exp (-2 * z - (c / 4) * z ^ 2 / h) := by
  have hh0 : 0 < h := by linarith
  have h₁ : (z - a) ^ 2 / (2 * h) ≤ (z - a) ^ 2 / H :=
    div_le_div_of_nonneg_left (sq_nonneg _) hH hHu
  have hpower : z ^ 2 / 2 - a ^ 2 ≤ (z - a) ^ 2 := by
    nlinarith [sq_nonneg (z - 2 * a)]
  have h₂ : z ^ 2 / (4 * h) - a ^ 2 / (2 * h) ≤ (z - a) ^ 2 / (2 * h) := by
    calc
      _ = (z ^ 2 / 2 - a ^ 2) / (2 * h) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hpower (by positivity)
  have h₃ : a ^ 2 / (2 * h) ≤ a ^ 2 / 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
  have hq : z ^ 2 / (4 * h) - a ^ 2 / 2 ≤ (z - a) ^ 2 / H := by
    linarith only [h₁, h₂, h₃]
  have hm := mul_le_mul_of_nonneg_left hq hc
  have he : Real.exp (-2 * (z - a) - c * (z - a) ^ 2 / H) ≤
      Real.exp (2 * a + c * a ^ 2 / 2) * Real.exp (-2 * z - (c / 4) * z ^ 2 / h) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      -2 * (z - a) - c * (z - a) ^ 2 / H =
          -2 * (z - a) - c * ((z - a) ^ 2 / H) := by ring
      _ ≤ -2 * (z - a) - c * (z ^ 2 / (4 * h) - a ^ 2 / 2) :=
        sub_le_sub_left hm _
      _ = (2 * a + c * a ^ 2 / 2) + (-2 * z - (c / 4) * z ^ 2 / h) := by
        field_simp [hh0.ne']
        <;> ring
  have hp : 1 + (z - a) ≤ 1 + z := by linarith
  have hb := mul_le_mul hp he (Real.exp_nonneg _) (show 0 ≤ 1 + z by linarith)
  have hb' := mul_le_mul_of_nonneg_left hb hD
  calc
    _ = D * ((1 + (z - a)) *
        Real.exp (-2 * (z - a) - c * (z - a) ^ 2 / H)) := by ring
    _ ≤ D * ((1 + z) * (Real.exp (2 * a + c * a ^ 2 / 2) *
        Real.exp (-2 * z - (c / 4) * z ^ 2 / h))) := hb'
    _ = (D * Real.exp (2 * a + c * a ^ 2 / 2)) * (1 + z) *
        Real.exp (-2 * z - (c / 4) * z ^ 2 / h) := by ring

/-- A fixed coefficient controls every probability in the compact shifted-height range. -/
theorem gaussian_compact_tail_envelope (c a z h : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hz : 0 ≤ z) (hza : z ≤ a) (hh : 1 ≤ h) :
    1 ≤ Real.exp (2 * a + c * a ^ 2) * (1 + z) * Real.exp (-2 * z - c * z ^ 2 / h) := by
  have hh0 : 0 < h := by linarith
  have hs : z ^ 2 ≤ a ^ 2 := by nlinarith
  have hq : c * z ^ 2 / h ≤ c * a ^ 2 := by
    apply (div_le_iff₀ hh0).mpr
    exact (mul_le_mul_of_nonneg_left hs hc).trans
      (le_mul_of_one_le_right (mul_nonneg hc (sq_nonneg a)) hh)
  have he : 1 ≤ Real.exp (2 * a + c * a ^ 2) * Real.exp (-2 * z - c * z ^ 2 / h) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by linarith)
  have hp : Real.exp (2 * a + c * a ^ 2) ≤
      Real.exp (2 * a + c * a ^ 2) * (1 + z) :=
    le_mul_of_one_le_right (Real.exp_nonneg _) (by linarith)
  exact he.trans (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _))

end SRWTightness
