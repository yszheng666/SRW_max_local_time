import SRWTightness.PairEndpointShift
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Moving the two site coefficients into the final Brownian node produces the cross terms. -/
theorem pairEndpointShift_quadratic {n : ℕ} (last : Fin n) (T x : Fin n → ℝ)
    (hmax : ∀ j, T j ≤ T last) (a b : ℝ) :
    (∑ j, ∑ l, pairEndpointShift last x a b j * min (T j) (T l) *
      pairEndpointShift last x a b l) =
      (∑ j, ∑ l, x j * min (T j) (T l) * x l) +
      2 * (a + b) * (∑ j, x j * T j) + (a + b) ^ 2 * T last := by
  have hrow (j : Fin n) : min (T last) (T j) = T j := min_eq_right (hmax j)
  have hcol (j : Fin n) : min (T j) (T last) = T j := min_eq_left (hmax j)
  simp only [pairEndpointShift, add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hrow, hcol]
  have hmul (c : ℝ) (j : Fin n) : c * T j * x j = c * (x j * T j) := by ring
  simp_rw [hmul]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

end SRWTightness
