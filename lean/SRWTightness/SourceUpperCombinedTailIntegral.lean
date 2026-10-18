import SRWTightness.SourceUpperCombinedTailEnvelope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set
namespace SRWTightness

/-- Integrating the shifted fine-field envelope against the actual residual law. -/
theorem source_upper_shifted_fine_tail_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (z h c : ℝ) (hh : 0 < h) (hc : 0 ≤ c) :
    (∫ u in Icc 0 z, (1 + (z - u)) *
      Real.exp (-2 * (z - u) - c * (z - u) ^ 2 / h) ∂ν) ≤
      ((1 + z) * Real.exp (-2 * z - c * z ^ 2 / (2 * h))) *
        ∫ u in Icc 0 z, Real.exp (2 * u + c * u ^ 2 / h) ∂ν := by
  rw [← integral_const_mul]
  apply setIntegral_mono_on
    (show Continuous (fun u : ℝ ↦ (1 + (z - u)) *
      Real.exp (-2 * (z - u) - c * (z - u) ^ 2 / h)) by
        fun_prop).continuousOn.integrableOn_Icc
    (show Continuous (fun u : ℝ ↦
      ((1 + z) * Real.exp (-2 * z - c * z ^ 2 / (2 * h))) *
        Real.exp (2 * u + c * u ^ 2 / h)) by
        fun_prop).continuousOn.integrableOn_Icc measurableSet_Icc
  intro u hu
  exact source_upper_shifted_fine_tail z u h c hu.1 hu.2 hh hc

end SRWTightness
