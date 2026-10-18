import SRWTightness.GaussianReflectionDensity
import SRWTightness.HalfLineReflectionIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Integrating the bridge reflection factor gives exactly the central Gaussian mass. -/
theorem gaussian_reflection_mass (s q : ℝ) (hs : 0 < s) (hq : 0 ≤ q) :
    (∫ b in Set.Iio q, gaussianPDFReal 0 s.toNNReal b *
      (1 - Real.exp (-(2 * q * (q - b) / s)))) =
      (gaussianReal 0 s.toNNReal).real (Set.Icc (-q) q) := by
  let f := gaussianPDFReal 0 s.toNNReal
  have hi : Integrable f := integrable_gaussianPDFReal 0 s.toNNReal
  have he (b : ℝ) : f (-b) = f b := by simp [f, gaussianPDFReal_def]
  have hw (b : ℝ) : f b * (1 - Real.exp (-(2 * q * (q - b) / s))) =
      f b - f (2 * q - b) := by
    rw [mul_sub, mul_one, gaussian_reflection_density s q b hs]
  change (∫ b in Set.Iio q, f b * (1 - Real.exp (-(2 * q * (q - b) / s)))) = _
  simp_rw [hw]
  rw [integral_sub hi.integrableOn (hi.comp_sub_left (2 * q)).integrableOn,
    half_line_reflection_integral f q (2 * q)]
  have hq' : 2 * q - q = q := by ring
  rw [hq']
  have hn := half_line_reflection_integral f (-q) 0
  simp only [zero_sub, he, neg_neg] at hn
  rw [← hn, intervalIntegral.integral_Iio_sub_Iio hi.integrableOn (by linarith)]
  change _ = (gaussianReal 0 s.toNNReal (Set.Icc (-q) q)).toReal
  rw [gaussianReal_apply_eq_integral 0 (ne_of_gt (Real.toNNReal_pos.mpr hs)),
    ENNReal.toReal_ofReal (integral_nonneg (fun b ↦ gaussianPDFReal_nonneg _ _ b))]
  rw [integral_Ico_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]

end SRWTightness
