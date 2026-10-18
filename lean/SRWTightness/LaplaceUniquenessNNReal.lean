import SRWTightness.LaplacePolynomialAlgebra

open MeasureTheory MvPolynomial BoundedContinuousFunction
open scoped NNReal BoundedContinuousFunction

namespace SRWTightness

 theorem laplacePolynomial_monomial_apply {ι : Type*} [Fintype ι]
    (d : ι →₀ ℕ) (a : ℝ) (x : ι → ℝ≥0) :
    (MvPolynomial.aeval laplaceCoordinate (MvPolynomial.monomial d a)) x =
      a * Real.exp (-(∑ i, (d i : ℝ) * (x i : ℝ))) := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i ↦ pow_zero _)]
  change a * (∏ i, (laplaceCoordinate i) ^ d i) x = _
  rw [BoundedContinuousFunction.prod_apply]
  simp only [BoundedContinuousFunction.pow_apply]
  change a * (∏ i, Real.exp (-(x i : ℝ)) ^ d i) = _
  simp_rw [← Real.exp_nat_mul]
  rw [← Real.exp_sum]
  congr 2
  simp only [mul_neg, Finset.sum_neg_distrib]

 theorem integral_laplacePolynomial_eq {ι : Type*} [Fintype ι]
    (μ ν : Measure (ι → ℝ≥0)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ι → ℕ,
      (∫ x, Real.exp (-(∑ i, (n i : ℝ) * (x i : ℝ))) ∂μ) =
        ∫ x, Real.exp (-(∑ i, (n i : ℝ) * (x i : ℝ))) ∂ν)
    (p : MvPolynomial ι ℝ) :
    (∫ x, (MvPolynomial.aeval laplaceCoordinate p) x ∂μ) =
      ∫ x, (MvPolynomial.aeval laplaceCoordinate p) x ∂ν := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    simp_rw [laplacePolynomial_monomial_apply]
    rw [integral_const_mul, integral_const_mul, h (fun i ↦ d i)]
  | add p q hp hq =>
    simp only [map_add, BoundedContinuousFunction.add_apply]
    rw [integral_add ((MvPolynomial.aeval laplaceCoordinate p).integrable μ)
      ((MvPolynomial.aeval laplaceCoordinate q).integrable μ),
      integral_add ((MvPolynomial.aeval laplaceCoordinate p).integrable ν)
      ((MvPolynomial.aeval laplaceCoordinate q).integrable ν), hp, hq]

/-- Finite measures on the nonnegative orthant are determined by their Laplace transforms.
The proof uses the point-separating algebra of bounded exponential-coordinate polynomials. -/
theorem measure_eq_of_laplace_eq_nnreal {ι : Type*} [Fintype ι]
    (μ ν : Measure (ι → ℝ≥0)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) →
      (∫ x, Real.exp (-(∑ i, f i * (x i : ℝ))) ∂μ) =
        ∫ x, Real.exp (-(∑ i, f i * (x i : ℝ))) ∂ν) : μ = ν := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
    (laplacePolynomialAlgebra_separates ι)
  intro g hg
  change g ∈ (MvPolynomial.aeval (laplaceCoordinate (ι := ι))).range at hg
  obtain ⟨p, rfl⟩ := hg
  exact integral_laplacePolynomial_eq μ ν
    (fun n ↦ h (fun i ↦ (n i : ℝ)) (fun i ↦ Nat.cast_nonneg _)) p

end SRWTightness
