import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- Generic conditioning and integration by parts for an independent Gaussian and a real law. -/
def GaussianPositiveConvolutionInput : Prop :=
  ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (v a : ℝ), 0 < v → 0 < a →
    IntegrableOn (fun z ↦ ν.real (Ici z) * Real.exp (-((a - z) ^ 2 / (2 * v))))
      (Icc 0 a) volume ∧
    ((gaussianReal 0 v.toNNReal).prod ν).real {p | a ≤ max p.1 0 + p.2} ≤
      (gaussianReal 0 v.toNNReal).real (Ici a) + ν.real (Ici a) +
        (1 / Real.sqrt v) *
          ∫ z in Icc 0 a, ν.real (Ici z) * Real.exp (-((a - z) ^ 2 / (2 * v)))

end SRWTightness
