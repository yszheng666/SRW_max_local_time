import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Gaussian integrability is equivalent to density-weighted Lebesgue integrability. -/
theorem gaussian_density_integrable_iff (m : ℝ) (v : NNReal) (hv : v ≠ 0)
    (f : ℝ → ℝ) :
    Integrable f (gaussianReal m v) ↔ Integrable (fun z ↦ gaussianPDFReal m v z * f z) := by
  rw [gaussianReal_of_var_ne_zero m hv]
  simpa only [toReal_gaussianPDF, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF m v)
      (ae_of_all _ (fun _ ↦ gaussianPDF_lt_top)) (g := f))

end SRWTightness
