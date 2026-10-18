import SRWTightness.ExponentialHolding

open MeasureTheory ProbabilityTheory Set

namespace SRWTightness

 theorem exponential_density_pow (k : ℕ) (t : ℝ) :
    (exponentialPDF 1 t).toReal * t ^ k =
      (Ici (0 : ℝ)).indicator (fun t ↦ Real.exp (-t) * t ^ k) t := by
  by_cases ht : 0 ≤ t
  · rw [exponentialPDF_of_nonneg ht, ENNReal.toReal_ofReal (by positivity),
      Set.indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht)]
    simp
  · rw [exponentialPDF_of_neg (lt_of_not_ge ht)]
    simp [Set.indicator_of_notMem (show t ∉ Ici (0 : ℝ) from ht)]

 theorem integrable_exponential_power (k : ℕ) :
    Integrable (fun t : ℝ ↦ t ^ k) (expMeasure 1) := by
  change Integrable _ (volume.withDensity (exponentialPDF 1))
  have hm : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul₀' hm.aemeasurable
    (Filter.Eventually.of_forall (fun t ↦ by simp [exponentialPDF]))]
  simp only [smul_eq_mul, exponential_density_pow]
  rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  have h := Real.GammaIntegral_convergent (by positivity : 0 < (k : ℝ) + 1)
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using h

 theorem integral_exponential_power (k : ℕ) :
    (∫ t : ℝ, t ^ k ∂expMeasure 1) = (k.factorial : ℝ) := by
  change (∫ t : ℝ, t ^ k ∂volume.withDensity (exponentialPDF 1)) = _
  have hm : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun t ↦ by simp [exponentialPDF]))]
  simp only [smul_eq_mul, exponential_density_pow]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have h := Real.Gamma_eq_integral (by positivity : 0 < (k : ℝ) + 1)
  rw [Real.Gamma_nat_eq_factorial] at h
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using h.symm

end SRWTightness
