import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

noncomputable def suffixSum {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin n, if k ≤ i.val then x i else 0

@[simp] theorem suffixSum_terminal {n : ℕ} (x : Fin n → ℝ) : suffixSum x n = 0 := by
  unfold suffixSum
  apply Finset.sum_eq_zero
  intro i _
  simp only [not_le.mpr i.isLt, ↓reduceIte]

theorem suffixSum_step {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    suffixSum x i.val = x i + suffixSum x (i.val + 1) := by
  have ht (j : Fin n) : (if i.val ≤ j.val then x j else 0) =
      (if j = i then x i else 0) + (if i.val + 1 ≤ j.val then x j else 0) := by
    by_cases he : j = i
    · subst j; simp
    · have hv : j.val ≠ i.val := fun h ↦ he (Fin.ext h)
      by_cases hij : i.val ≤ j.val
      · have hh : i.val + 1 ≤ j.val := by omega
        simp [he, hij, hh]
      · have hh : ¬ i.val + 1 ≤ j.val := by omega
        simp [he, hij, hh]
  simp only [suffixSum, ht, Finset.sum_add_distrib]
  simp

theorem suffixSum_shift_square_sum_le {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, suffixSum x (i.val + 1) ^ 2) ≤ ∑ i : Fin n, suffixSum x i.val ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ suffixSum x (k + 1) ^ 2),
    Fin.sum_univ_eq_sum_range (fun k ↦ suffixSum x k ^ 2)]
  have he := Finset.sum_range_succ' (fun k ↦ suffixSum x k ^ 2) n
  rw [Finset.sum_range_succ, suffixSum_terminal, sq, zero_mul, add_zero] at he
  linarith [sq_nonneg (suffixSum x 0)]

/-- The inverse cumulative-sum map has squared Euclidean norm at most four. -/
theorem square_sum_le_four_suffix_energy {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, x i ^ 2) ≤ 4 * ∑ i : Fin n, suffixSum x i.val ^ 2 := by
  have hp (i : Fin n) : x i ^ 2 ≤ 2 * suffixSum x i.val ^ 2 + 2 * suffixSum x (i.val + 1) ^ 2 := by
    have hs := suffixSum_step x i
    rw [show x i = suffixSum x i.val - suffixSum x (i.val + 1) by linarith]
    nlinarith [sq_nonneg (suffixSum x i.val + suffixSum x (i.val + 1))]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hp i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  linarith [suffixSum_shift_square_sum_le x]

end SRWTightness
