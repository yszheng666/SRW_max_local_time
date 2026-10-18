import SRWTightness.GaussianDensityProductIdentity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A product of two nondegenerate Gaussian densities is integrable. -/
theorem gaussian_density_product_integrable (s t x y : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Integrable (fun z ↦ gaussianPDFReal x s.toNNReal z * gaussianPDFReal y t.toNNReal z) := by
  simp_rw [gaussian_density_product_identity s t x y _ hs ht]
  exact (integrable_gaussianPDFReal _ _).const_mul _

/-- The full-line Gaussian convolution is the density at the sum of the two times. -/
theorem gaussian_density_convolution (s t x y : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (∫ z, gaussianPDFReal x s.toNNReal z * gaussianPDFReal y t.toNNReal z) =
      gaussianPDFReal x (s + t).toNNReal y := by
  have hv : (s * t / (s + t)).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (by positivity))
  simp_rw [gaussian_density_product_identity s t x y _ hs ht]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ hv, mul_one]

end SRWTightness
