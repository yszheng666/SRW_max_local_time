import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Matrix
namespace SRWTightness

/-- Generic finite Gaussian chaining on a bounded planar set, with a zero-variance anchor. -/
def PlanarGaussianIncrementSupInput : Prop :=
  ∀ L K : ℝ, 0 < L → 0 < K → ∃ A b : ℝ, 0 < A ∧ 0 < b ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
      (J : Finset ι) (o : ι) (p : ι → ℝ × ℝ) (r : ℝ),
      S.PosSemidef → o ∈ J → S o o = 0 → 0 < r →
      (∀ x ∈ J, (p x).1 ^ 2 + (p x).2 ^ 2 ≤ (K * r) ^ 2) →
      (∀ x ∈ J, ∀ y ∈ J, S x x + S y y - 2 * S x y ≤
        L * (((p x).1 - (p y).1) ^ 2 + ((p x).2 - (p y).2) ^ 2) / r ^ 2) →
      ∀ u : ℝ, 0 ≤ u →
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
          {φ | ∃ x ∈ J, u ≤ |φ x|} ≤ A * Real.exp (-b * u ^ 2)

end SRWTightness
