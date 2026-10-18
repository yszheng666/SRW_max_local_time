import SRWTightness.GaussianMillsEnvelope
import SRWTightness.GaussianMiddleKernelBound
import SRWTightness.ExternalGaussianMills

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- The full original scalar Mills bound follows internally from density and tangent-tail
integration. -/
theorem gaussian_mills_input_internal : GaussianMillsInput := by
  intro v a hv ha
  have ht := gaussian_tangent_tail_integral v a hv ha
  let L : ℝ := (1 / Real.sqrt v) * Real.exp (-(a ^ 2 / (2 * v)))
  have hi := ht.1.const_mul L
  have hp : ∀ x : ℝ, gaussianPDFReal 0 v.toNNReal x ≤
      L * Real.exp (-(a / v) * (x - a)) := by
    intro x
    have hb := mul_le_mul_of_nonneg_left (gaussian_quadratic_tangent_envelope v a x hv)
      (by positivity : 0 ≤ 1 / Real.sqrt v)
    exact (gaussian_real_density_kernel_bound v hv x).trans (by
      simpa only [L, mul_assoc] using hb)
  have hpdf : IntegrableOn (gaussianPDFReal 0 v.toNNReal) (Ici a) volume :=
    (integrable_gaussianPDFReal 0 v.toNNReal).integrableOn
  have hbound := setIntegral_mono_on hpdf hi measurableSet_Ici (fun x _ ↦ hp x)
  rw [integral_const_mul, ht.2] at hbound
  have hmass := gaussian_real_set_integral_density (fun _ : ℝ ↦ (1 : ℝ))
    (Ici a) measurableSet_Ici v hv
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hmass
  rw [hmass]
  have hcoef : (1 / Real.sqrt v) * (v / a) = Real.sqrt v / a := by
    have hs := Real.sq_sqrt hv.le
    field_simp [(Real.sqrt_pos.mpr hv).ne', ha.ne']
    nlinarith
  have he : L * (v / a) = Real.sqrt v / a * Real.exp (-a ^ 2 / (2 * v)) := by
    dsimp [L]
    rw [show (1 / Real.sqrt v) * Real.exp (-(a ^ 2 / (2 * v))) * (v / a) =
      ((1 / Real.sqrt v) * (v / a)) * Real.exp (-(a ^ 2 / (2 * v))) by ring, hcoef]
    simp only [neg_div]
  exact hbound.trans_eq he

end SRWTightness
