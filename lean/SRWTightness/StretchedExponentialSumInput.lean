import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace SRWTightness

/-- Standard uniform integral-test bound on positively separated meshes away from zero.
This is an explicit foundational hypothesis, independent of the SRW model. -/
def SeparatedStretchedExponentialSumInput : Prop :=
  ∀ δ h₀ c γ : ℝ, 0 < δ → 0 < h₀ → 0 < c → 0 < γ →
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (x : ℕ → ℝ),
      (∀ i ≤ N, h₀ ≤ x i) → (∀ i < N, δ ≤ x (i + 1) - x i) →
      (∑ i ∈ Finset.range (N + 1),
        ((1 + (x i) ^ γ) / x i) * Real.exp (-c * (x i) ^ γ)) ≤ C

/-- Standard domination of a quadratic polynomial by a stretched exponential. -/
def QuadraticStretchedExponentialBoundInput : Prop :=
  ∀ c γ : ℝ, 0 < c → 0 < γ → ∃ C : ℝ, 0 < C ∧
    ∀ d : ℝ, 1 ≤ d → d ^ 2 * Real.exp (-c * d ^ γ) ≤ C

end SRWTightness
