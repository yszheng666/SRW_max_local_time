import SRWTightness.GaussianQuadraticLaplace
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Independent equal-variance Gaussian coordinates have the exact radial Laplace transform. -/
theorem gaussian_vector_quadratic_laplace {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    (∫ z : ι → ℝ, Real.exp (-t * ∑ i, (z i) ^ 2)
      ∂Measure.pi (fun i ↦ gaussianReal (m i) s.toNNReal)) =
        Real.exp (-t * (∑ i, (m i) ^ 2) / (1 + 2 * s * t)) /
          (Real.sqrt (1 + 2 * s * t)) ^ Fintype.card ι := by
  classical
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun (_ : ι) (z : ℝ) ↦ Real.exp (-t * z ^ 2))]
  simp_rw [gaussian_quadratic_laplace_integral _ s t hs ht]
  rw [Finset.prod_div_distrib, ← Real.exp_sum]
  simp only [Finset.prod_const, Finset.card_univ]
  congr 2
  rw [Finset.sum_div]

end SRWTightness
