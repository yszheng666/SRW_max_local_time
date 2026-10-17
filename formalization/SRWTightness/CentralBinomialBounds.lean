import SRWTightness.CentralBinomialWallis

namespace SRWTightness

theorem centralBinomialRatio_sq_lower (n : ℕ) :
    2 / (Real.pi * (2 * (n : ℝ) + 1)) ≤ centralBinomialRatio n ^ 2 := by
  rw [centralBinomialRatio_sq]
  have h := one_div_le_one_div_of_le
    (mul_pos (by positivity : 0 < 2 * (n : ℝ) + 1) (Real.Wallis.W_pos n))
    (mul_le_mul_of_nonneg_left (Real.Wallis.W_le n) (by positivity : 0 ≤ 2 * (n : ℝ) + 1))
  calc
    _ = 1 / ((2 * (n : ℝ) + 1) * (Real.pi / 2)) := by field_simp <;> ring
    _ ≤ _ := h

theorem centralBinomialRatio_sq_upper (n : ℕ) :
    centralBinomialRatio n ^ 2 ≤ (4 * (n : ℝ) + 4) / (Real.pi * (2 * n + 1) ^ 2) := by
  rw [centralBinomialRatio_sq]
  have h := one_div_le_one_div_of_le
    (mul_pos (by positivity : 0 < 2 * (n : ℝ) + 1)
      (by positivity : 0 < (2 * (n : ℝ) + 1) / (2 * n + 2) * (Real.pi / 2)))
    (mul_le_mul_of_nonneg_left (Real.Wallis.le_W n) (by positivity : 0 ≤ 2 * (n : ℝ) + 1))
  calc
    _ ≤ 1 / ((2 * (n : ℝ) + 1) * ((2 * n + 1) / (2 * n + 2) * (Real.pi / 2))) := h
    _ = _ := by field_simp <;> ring

theorem nat_mul_centralBinomialRatio_sq_le (n : ℕ) :
    (n : ℝ) * centralBinomialRatio n ^ 2 ≤ 1 / Real.pi := by
  calc
    _ ≤ (n : ℝ) * ((4 * n + 4) / (Real.pi * (2 * n + 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left (centralBinomialRatio_sq_upper n) (Nat.cast_nonneg n)
    _ ≤ _ := by
      have hp := Real.pi_pos
      have h1 : 0 < (2 * (n : ℝ) + 1) ^ 2 := by positivity
      rw [← mul_div_assoc, div_le_div_iff₀ (mul_pos hp h1) hp]
      nlinarith

theorem nat_mul_centralBinomialRatio_sq_error (n : ℕ) :
    |(n : ℝ) * centralBinomialRatio n ^ 2 - 1 / Real.pi| ≤
      1 / (Real.pi * (2 * n + 1)) := by
  rw [abs_of_nonpos (sub_nonpos.mpr (nat_mul_centralBinomialRatio_sq_le n))]
  have h := mul_le_mul_of_nonneg_left (centralBinomialRatio_sq_lower n) (Nat.cast_nonneg n)
  have he : (n : ℝ) * (2 / (Real.pi * (2 * n + 1))) =
      1 / Real.pi - 1 / (Real.pi * (2 * n + 1)) := by
    have hp := Real.pi_ne_zero
    have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    <;> ring
  rw [he] at h
  linarith

end SRWTightness
