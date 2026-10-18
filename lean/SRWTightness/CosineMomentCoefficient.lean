import SRWTightness.CosineMomentBinomial

open Finset

namespace SRWTightness

theorem cosineMoment_coefficient (n j : ℕ) (hj : j ≤ n) :
    cosineMoment n (2 * (j : ℤ) - n) = 2 * Real.pi * (n.choose j : ℝ) / 2 ^ n := by
  have h := cosineMoment_binomial_sum n (2 * (j : ℤ) - n)
  have hplus (i : ℕ) : 2 * (i : ℤ) - n + (2 * (j : ℤ) - n) = 0 ↔ i = n - j := by omega
  have hminus (i : ℕ) : 2 * (i : ℤ) - n - (2 * (j : ℤ) - n) = 0 ↔ i = j := by omega
  simp_rw [hplus, hminus, mul_add, sum_add_distrib, mul_ite, mul_one, mul_zero] at h
  have hjr : j ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le hj)
  have hnj : n - j ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n j))
  simp only [sum_ite_eq', hjr, hnj, if_true, Nat.choose_symm hj] at h
  apply (eq_div_iff (by positivity : (2 : ℝ) ^ n ≠ 0)).2
  nlinarith [h]

end SRWTightness
