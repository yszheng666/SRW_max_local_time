import SRWTightness.GaussianQuadraticLaplace

open ProbabilityTheory
namespace SRWTightness

/-- A quadratic weight of a Gaussian density is an exactly rescaled Gaussian density. -/
theorem gaussian_quadratic_tilt_density (x s t z : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    gaussianPDFReal x s.toNNReal z * Real.exp (-t * z ^ 2) =
      (Real.exp (-t * x ^ 2 / (1 + 2 * s * t)) / Real.sqrt (1 + 2 * s * t)) *
        gaussianPDFReal (x / (1 + 2 * s * t)) (s / (1 + 2 * s * t)).toNNReal z := by
  have ha : 0 < 1 + 2 * s * t := by positivity
  have hv : 0 < s / (1 + 2 * s * t) := div_pos hs ha
  simp only [gaussianPDFReal_def, Real.coe_toNNReal s hs.le,
    Real.coe_toNNReal _ hv.le]
  have hsqrt : Real.sqrt (2 * Real.pi * (s / (1 + 2 * s * t))) =
      Real.sqrt (2 * Real.pi * s) / Real.sqrt (1 + 2 * s * t) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi * s)]
    congr 1
    ring
  rw [hsqrt]
  have he := gaussian_quadratic_laplace_square x s t z hs ht
  have harg : -(z - x / (1 + 2 * s * t)) ^ 2 / (2 * (s / (1 + 2 * s * t))) =
      -((1 + 2 * s * t) / (2 * s)) * (z - x / (1 + 2 * s * t)) ^ 2 := by
    field_simp
    <;> ring
  rw [harg, mul_assoc, ← Real.exp_add]
  rw [show -(z - x) ^ 2 / (2 * s) + -t * z ^ 2 =
    -(z - x) ^ 2 / (2 * s) - t * z ^ 2 by ring, he, Real.exp_sub]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  have hS : Real.sqrt (1 + 2 * s * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hP : Real.sqrt (2 * Real.pi * s) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp
  <;> ring

end SRWTightness
