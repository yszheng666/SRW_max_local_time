import SRWTightness.RootLogGeneratingError

namespace SRWTightness

/-- Replace the exact first mean by two with an explicit weighted absolute error. -/
theorem root_log_mean_replacement (m C r k s δ L : ℝ)
    (hm : 0 ≤ m) (hm3 : m ≤ 3) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hk : 0 ≤ k) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (he : k * |m - 2| ≤ δ)
    (hb : L ≤ k * (m * s + m * (2 + 8 * (C * r)) * s ^ 2)) :
    L ≤ 2 * k * s + (6 + 24 * C) * k * r * s ^ 2 + δ := by
  have hδ : 0 ≤ δ := (mul_nonneg hk (abs_nonneg _)).trans he
  have hlin : k * (m - 2) * s ≤ δ := by
    calc
      _ ≤ k * |m - 2| * s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) hk) hs
      _ ≤ δ * s := mul_le_mul_of_nonneg_right he hs
      _ ≤ δ := mul_le_of_le_one_right hδ hs1
  have hcoef : m * (2 + 8 * (C * r)) ≤ (6 + 24 * C) * r := by
    calc
      _ ≤ 3 * (2 + 8 * (C * r)) :=
        mul_le_mul_of_nonneg_right hm3 (by positivity)
      _ ≤ (6 + 24 * C) * r := by nlinarith
  have hquad := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoef hk) (sq_nonneg s)
  nlinarith only [hb, hlin, hquad]

end SRWTightness
