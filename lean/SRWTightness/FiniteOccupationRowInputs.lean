import SRWTightness.MarkSumGenerating

open MeasureTheory Matrix

namespace SRWTightness

/-- Standard finite killed-occupation integrability throughout the positive row-contraction region.
This explicit foundational input contains no manuscript scale or tail conclusion. -/
def FiniteOccupationRowIntegrabilityInput : Prop :=
  ∀ (D A : Finset Site), A ⊆ D → ∀ v : A → ℝ, (∀ z, 1 ≤ v z) →
    (∀ y : A, ∑ z : A,
      |killedGreen D y z - (if y = z then 1 else 0)| * |v z - 1| < 1) →
    ∀ x : Site, Integrable (fun ω ↦ markMonomial v (killedMark D A x ω)) pathLaw

/-- Standard finite-dimensional Neumann inverse estimate in the maximum row norm. -/
def FiniteResolventRowBoundInput : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ℝ),
    0 ≤ q → q < 1 → (∀ i, ∑ j, |M i j| ≤ q) →
    ∀ i, |((1 - M)⁻¹.mulVec 1) i| ≤ 1 / (1 - q)

end SRWTightness
