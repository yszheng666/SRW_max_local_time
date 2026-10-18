import SRWTightness.FiniteProductDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

 theorem standardGaussianPi_withDensity {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι ↦ gaussianReal 0 1) =
      (volume : Measure (ι → ℝ)).withDensity (fun x ↦ ∏ i, gaussianPDF 0 1 (x i)) := by
  have hg : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  letI : IsProbabilityMeasure (volume.withDensity (gaussianPDF 0 1)) := by
    rw [← hg]
    infer_instance
  change Measure.pi (fun _ : ι ↦ gaussianReal 0 1) =
    (Measure.pi (fun _ : ι ↦ (volume : Measure ℝ))).withDensity
      (fun x ↦ ∏ i, gaussianPDF 0 1 (x i))
  simpa only [← hg] using finite_product_withDensity (fun _ : ι ↦ (volume : Measure ℝ))
    (fun _ : ι ↦ gaussianPDF 0 1) (fun _ ↦ measurable_gaussianPDF 0 1)

 theorem standardGaussianPi_integral {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℝ) :
    (∫ x, F x ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
        ∫ x : ι → ℝ, Real.exp (-(∑ i, x i ^ 2) / 2) * F x := by
  rw [standardGaussianPi_withDensity]
  have hm : Measurable (fun x : ι → ℝ ↦ ∏ i, gaussianPDF 0 1 (x i)) := by
    apply Finset.measurable_prod
    intro i hi
    exact (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun x ↦ ENNReal.prod_lt_top (fun i hi ↦ gaussianPDF_lt_top))) F]
  have he (x : ι → ℝ) : (∏ i, gaussianPDF 0 1 (x i)).toReal =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι * Real.exp (-(∑ i, x i ^ 2) / 2) := by
    simp only [ENNReal.toReal_prod, toReal_gaussianPDF, gaussianPDFReal, NNReal.coe_one,
      sub_zero, mul_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← Real.exp_sum, ← Finset.sum_div, Finset.sum_neg_distrib]
  simp_rw [he, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]

end SRWTightness
