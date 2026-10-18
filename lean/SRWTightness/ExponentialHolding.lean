import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory ProbabilityTheory Set

namespace SRWTightness

 theorem exponential_holding_laplace (f : ℝ) (hf : 0 ≤ f) :
    (∫ t : ℝ, Real.exp (-f * t) ∂expMeasure 1) = (1 + f)⁻¹ := by
  change (∫ t : ℝ, Real.exp (-f * t) ∂volume.withDensity (exponentialPDF 1)) = _
  have hm : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun t ↦ by simp [exponentialPDF]))]
  simp only [smul_eq_mul]
  have he (t : ℝ) : (exponentialPDF 1 t).toReal * Real.exp (-f * t) =
      (Ici (0 : ℝ)).indicator (fun t ↦ Real.exp (-(1 + f) * t)) t := by
    by_cases ht : 0 ≤ t
    · rw [exponentialPDF_of_nonneg ht, ENNReal.toReal_ofReal (by positivity),
        Set.indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht)]
      simp only [one_mul, ← Real.exp_add]
      congr 1
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge ht)]
      simp [Set.indicator_of_notMem (show t ∉ Ici (0 : ℝ) from ht)]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (by linarith : -(1 + f) < 0)]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]

end SRWTightness
