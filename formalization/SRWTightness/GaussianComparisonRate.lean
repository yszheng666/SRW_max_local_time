import SRWTightness.SourceNormalApproximationRate

open Filter
open scoped Topology

namespace SRWTightness

/-- Under the source dimension bound, combined Gaussian errors fit the d^5/t rate. -/
theorem gaussian_comparison_rate_bound (p : ℕ) (C M P a d t : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hP : 0 ≤ P) (ha : 0 < a)
    (hd : 1 ≤ d) (ht : 0 ≤ t) (hp : (p : ℝ) ≤ P * d) :
    2 * (p * (C * d ^ 3 / t) / a) +
      2 * (Real.sqrt p * (M * d ^ 3 / t) / Real.sqrt a) ≤
      (2 * P * C / a + 2 * P * M / Real.sqrt a) * d ^ 5 / t := by
  have hpS : Real.sqrt (p : ℝ) ≤ p := by
    apply Real.sqrt_le_self_iff.mpr
    by_cases h : p = 0
    · exact Or.inl (by simp [h])
    · exact Or.inr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)
  have hd0 : 0 ≤ d := by linarith
  have hc := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp (show 0 ≤ C * d ^ 3 / t by positivity)) ha.le)
    (show (0 : ℝ) ≤ 2 by norm_num)
  have hm := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hpS.trans hp)
        (show 0 ≤ M * d ^ 3 / t by positivity)) (Real.sqrt_nonneg a))
    (show (0 : ℝ) ≤ 2 by norm_num)
  have hd45 : d ^ 4 ≤ d ^ 5 := by
    have hh := mul_le_mul_of_nonneg_right hd (pow_nonneg hd0 4)
    nlinarith
  calc
    _ ≤ 2 * (P * d * (C * d ^ 3 / t) / a) +
        2 * (P * d * (M * d ^ 3 / t) / Real.sqrt a) := add_le_add hc hm
    _ = (2 * P * C / a + 2 * P * M / Real.sqrt a) * d ^ 4 / t := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd45 (by positivity)) ht

end SRWTightness
