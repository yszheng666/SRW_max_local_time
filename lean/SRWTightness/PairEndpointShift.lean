import SRWTightness.PairObservationWeights

namespace SRWTightness

/-- In the Brownian block, both site coefficients add to the last retained average coefficient. -/
def pairEndpointShift {n : ℕ} (last : Fin n) (x : Fin n → ℝ) (a b : ℝ) : Fin n → ℝ :=
  fun j ↦ x j + if j = last then a + b else 0

/-- The endpoint change of coordinates has a bound independent of the number of averages. -/
theorem pairEndpointShift_norm_bound {n : ℕ} (last : Fin n) (x : Fin n → ℝ) (a b : ℝ) :
    (∑ j, x j ^ 2) + a ^ 2 + b ^ 2 ≤
      2 * (∑ j, pairEndpointShift last x a b j ^ 2) + 5 * (a ^ 2 + b ^ 2) := by
  have hp (j : Fin n) : x j ^ 2 ≤ 2 * pairEndpointShift last x a b j ^ 2 +
      if j = last then 4 * (a ^ 2 + b ^ 2) else 0 := by
    by_cases hj : j = last
    · subst j
      simp only [pairEndpointShift, if_true]
      nlinarith [sq_nonneg (x last + 2 * (a + b)), sq_nonneg (a - b)]
    · simp only [pairEndpointShift, hj, if_false, add_zero]
      nlinarith [sq_nonneg (x j)]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hp j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  linarith

/-- A Brownian one-quarter lower bound plus a unit residual bound controls the full vector. -/
theorem pairEndpointShift_energy_lower {n : ℕ} (last : Fin n)
    (x : Fin n → ℝ) (a b Q : ℝ)
    (hQ : (1 / 4 : ℝ) * (∑ j, pairEndpointShift last x a b j ^ 2) +
      (a ^ 2 + b ^ 2) ≤ Q) :
    (1 / 8 : ℝ) * ((∑ j, x j ^ 2) + a ^ 2 + b ^ 2) ≤ Q := by
  have hs := pairEndpointShift_norm_bound last x a b
  nlinarith [sq_nonneg a, sq_nonneg b]

end SRWTightness
