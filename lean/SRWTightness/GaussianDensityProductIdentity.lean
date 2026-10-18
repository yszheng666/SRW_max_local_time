import SRWTightness.GaussianQuadraticTiltDensity

open ProbabilityTheory
namespace SRWTightness

/-- Completing the square gives the exact product of two nondegenerate Gaussian densities. -/
theorem gaussian_density_product_identity (s t x y z : ℝ) (hs : 0 < s) (ht : 0 < t) :
    gaussianPDFReal x s.toNNReal z * gaussianPDFReal y t.toNNReal z =
      gaussianPDFReal x (s + t).toNNReal y *
        gaussianPDFReal ((t * x + s * y) / (s + t)) (s * t / (s + t)).toNNReal z := by
  have hst : 0 < s + t := add_pos hs ht
  have hv : 0 < s * t / (s + t) := by positivity
  have he : -(z - x) ^ 2 / (2 * s) + -(z - y) ^ 2 / (2 * t) =
      -(y - x) ^ 2 / (2 * (s + t)) +
        -(z - (t * x + s * y) / (s + t)) ^ 2 / (2 * (s * t / (s + t))) := by
    field_simp
    <;> ring
  have hn : Real.sqrt (2 * Real.pi * s) * Real.sqrt (2 * Real.pi * t) =
      Real.sqrt (2 * Real.pi * (s + t)) *
        Real.sqrt (2 * Real.pi * (s * t / (s + t))) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi * s),
      ← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi * (s + t))]
    congr 1
    field_simp
    <;> ring
  simp only [gaussianPDFReal_def, Real.coe_toNNReal s hs.le,
    Real.coe_toNNReal t ht.le, Real.coe_toNNReal _ hst.le, Real.coe_toNNReal _ hv.le]
  calc
    _ = (Real.sqrt (2 * Real.pi * s) * Real.sqrt (2 * Real.pi * t))⁻¹ *
        Real.exp (-(z - x) ^ 2 / (2 * s) + -(z - y) ^ 2 / (2 * t)) := by
      rw [Real.exp_add, mul_inv_rev]
      ring
    _ = _ := by
      rw [he, hn, Real.exp_add, mul_inv_rev]
      ring

end SRWTightness
