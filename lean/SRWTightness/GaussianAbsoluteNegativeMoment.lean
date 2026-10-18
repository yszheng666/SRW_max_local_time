import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory ProbabilityTheory Set

open scoped NNReal

namespace SRWTightness

/-- Absolute powers with exponent above minus one are integrable against a Gaussian weight. -/
theorem integrable_abs_rpow_gaussian_weight (b p : ℝ) (hb : 0 < b) (hp : -1 < p) :
    Integrable (fun x : ℝ ↦ |x| ^ p * Real.exp (-b * x ^ 2)) volume := by
  have hpos : IntegrableOn (fun x : ℝ ↦ |x| ^ p * Real.exp (-b * x ^ 2)) (Ioi 0) := by
    apply (integrableOn_rpow_mul_exp_neg_mul_sq hb hp).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_of_pos hx]
  have hneg : IntegrableOn (fun x : ℝ ↦ |x| ^ p * Real.exp (-b * x ^ 2)) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, abs_neg, neg_sq, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨hneg, hpos⟩

/-- In particular, the inverse square-root absolute moment of a standard Gaussian is finite. -/
theorem gaussian_standard_inverse_half_integrable :
    Integrable (fun x : ℝ ↦ |x| ^ (-(1 / 2 : ℝ))) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x ↦ gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal, NNReal.coe_one,
    mul_one, sub_zero]
  have hh := integrable_abs_rpow_gaussian_weight (1 / 2) (-(1 / 2 : ℝ))
    (by norm_num) (by norm_num)
  convert hh.const_mul (Real.sqrt (2 * Real.pi))⁻¹ using 1 <;> try rfl
  funext x
  have he : -(x ^ 2) / 2 = -(1 / 2 : ℝ) * x ^ 2 := by ring
  rw [he]
  ring

end SRWTightness
