import SRWTightness.GrowingRecordDomains
import Mathlib.Algebra.Order.Field.GeomSum

open scoped BigOperators

namespace SRWTightness

/-- Reciprocal source radii have a depth-independent summable bound. -/
theorem growing_record_reciprocal_sum (m : ℝ) (hm : 0 < m) (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / growingRecordRadius m i) ≤ 2 / m := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hgeom : (∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) ≤ 2 := by
    have hh := geom_sum_Ico_le_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num) (m := 0) (n := n)
    norm_num [Nat.Ico_zero_eq_range] at hh ⊢
    exact hh
  calc
    _ ≤ ∑ i ∈ Finset.range n, (1 / m) * (1 / 2 : ℝ) ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      have hexp : (2 : ℝ) ^ i ≤ Real.exp (i : ℝ) := by
        have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he i
        simpa only [← Real.exp_nat_mul, mul_one] using hh
      have hh := one_div_le_one_div_of_le (mul_pos hm (pow_pos (by norm_num) i))
        (mul_le_mul_of_nonneg_left hexp hm.le)
      simpa only [growingRecordRadius, one_div_mul_one_div, one_div_pow] using hh
    _ = (1 / m) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
    _ ≤ (1 / m) * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 2 / m := by ring

end SRWTightness
