import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Set
namespace SRWTightness

/-- Generic tail-to-moment estimate for the positive part of a real random variable. -/
def SubGaussianPositiveMomentInput : Prop :=
  ∀ A b : ℝ, 0 < A → 0 < b → ∃ M : ℝ, 0 < M ∧
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      (∀ u : ℝ, 0 ≤ u → ν.real (Ici u) ≤ A * Real.exp (-b * u ^ 2)) →
      Integrable (fun u ↦ Real.exp (2 * max u 0 + b / 2 * (max u 0) ^ 2)) ν ∧
      (∫ u, Real.exp (2 * max u 0 + b / 2 * (max u 0) ^ 2) ∂ν) ≤ M

end SRWTightness
