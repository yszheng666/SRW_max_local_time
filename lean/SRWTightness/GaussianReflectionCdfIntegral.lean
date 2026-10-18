import SRWTightness.GaussianReflectionMass

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Integrating the explicit bridge reflection factor up to an endpoint gives the reflection CDF. -/
theorem gaussian_reflection_cdf_integral (T q b : ℝ) (hT : 0 < T) :
    (∫ y in Set.Iic b, gaussianPDFReal 0 T.toNNReal y *
      (1 - Real.exp (-(2 * q * (q - y) / T)))) =
      (gaussianReal 0 T.toNNReal).real (Set.Iic b) -
        (gaussianReal 0 T.toNNReal).real (Set.Ici (2 * q - b)) := by
  let f := gaussianPDFReal 0 T.toNNReal
  have hi : Integrable f := integrable_gaussianPDFReal 0 T.toNNReal
  have hw (y : ℝ) : f y * (1 - Real.exp (-(2 * q * (q - y) / T))) =
      f y - f (2 * q - y) := by
    rw [mul_sub, mul_one, gaussian_reflection_density T q y hT]
  have hp (A : Set ℝ) : (gaussianReal 0 T.toNNReal).real A = ∫ y in A, f y := by
    rw [Measure.real, gaussianReal_apply_eq_integral 0 (ne_of_gt (Real.toNNReal_pos.mpr hT)),
      ENNReal.toReal_ofReal (integral_nonneg (fun y ↦ gaussianPDFReal_nonneg _ _ y))]
  change (∫ y in Set.Iic b, f y * (1 - Real.exp (-(2 * q * (q - y) / T)))) = _
  simp_rw [hw]
  rw [integral_Iic_eq_integral_Iio,
    integral_sub hi.integrableOn (hi.comp_sub_left (2 * q)).integrableOn,
    half_line_reflection_integral f b (2 * q), hp, hp,
    integral_Iic_eq_integral_Iio, integral_Ici_eq_integral_Ioi]

end SRWTightness
