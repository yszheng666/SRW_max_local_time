import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory Set
namespace SRWTightness

/-- Standard conditioning bound for a sum with an independent nonnegative second coordinate. -/
def PositiveConvolutionInput : Prop :=
  ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    (∀ᵐ u ∂ν, 0 ≤ u) → ∀ z : ℝ, 0 ≤ z →
      IntegrableOn (fun u ↦ μ.real (Ici (z - u))) (Icc 0 z) ν ∧
      (μ.prod ν).real {p | z ≤ p.1 + p.2} ≤
        ν.real (Ici z) + ∫ u in Icc 0 z, μ.real (Ici (z - u)) ∂ν

end SRWTightness
