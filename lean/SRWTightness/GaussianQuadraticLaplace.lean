import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Completion of the square for a nonnegative quadratic Gaussian Laplace weight. -/
theorem gaussian_quadratic_laplace_square (x s t z : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    -(z - x) ^ 2 / (2 * s) - t * z ^ 2 =
      -((1 + 2 * s * t) / (2 * s)) * (z - x / (1 + 2 * s * t)) ^ 2 -
        t * x ^ 2 / (1 + 2 * s * t) := by
  have ha : 0 < 1 + 2 * s * t := by positivity
  field_simp
  <;> ring

/-- The actual one-dimensional Gaussian quadratic Laplace transform. -/
theorem gaussian_quadratic_laplace_integral (x s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    (∫ z : ℝ, Real.exp (-t * z ^ 2) ∂gaussianReal x s.toNNReal) =
      Real.exp (-t * x ^ 2 / (1 + 2 * s * t)) / Real.sqrt (1 + 2 * s * t) := by
  have hv : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  have ha : 0 < 1 + 2 * s * t := by positivity
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul, gaussianPDFReal, Real.coe_toNNReal _ hs.le]
  have he (z : ℝ) :
      (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(z - x) ^ 2 / (2 * s)) *
          Real.exp (-t * z ^ 2) =
        ((Real.sqrt (2 * Real.pi * s))⁻¹ *
          Real.exp (-t * x ^ 2 / (1 + 2 * s * t))) *
          Real.exp (-((1 + 2 * s * t) / (2 * s)) *
            (z - x / (1 + 2 * s * t)) ^ 2) := by
    rw [mul_assoc, ← Real.exp_add]
    have hh := gaussian_quadratic_laplace_square x s t z hs ht
    rw [show -(z - x) ^ 2 / (2 * s) + -t * z ^ 2 =
      -(z - x) ^ 2 / (2 * s) - t * z ^ 2 by ring, hh]
    rw [Real.exp_sub]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun z : ℝ ↦ Real.exp (-((1 + 2 * s * t) / (2 * s)) * z ^ 2)), integral_gaussian]
  have hsqrt : Real.sqrt (Real.pi / ((1 + 2 * s * t) / (2 * s))) =
      Real.sqrt (2 * Real.pi * s) / Real.sqrt (1 + 2 * s * t) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi * s)]
    congr 1
    field_simp
    <;> ring
  rw [hsqrt]
  have hp : Real.sqrt (2 * Real.pi * s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

end SRWTightness
