import SRWTightness.GaussianWhiteningTransport
import SRWTightness.IndependentVectorCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- External input: the finite-family form of Raic Theorem 1.1, source (3.4).
This is a proposition supplied as a theorem parameter, with no global inhabitant. -/
def RaicConvexCLTInput (Ω : Type*) [MeasurableSpace Ω]
    (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ (n : ℕ) (X : Fin n → Ω → EuclideanSpace ℝ ι),
      (∀ j, Measurable (X j)) →
      iIndepFun X ρ →
      (∀ j, Integrable (X j) ρ ∧ (∫ ω, X j ω ∂ρ) = 0 ∧ MemLp (X j) 2 ρ) →
      (∀ r s : ι, (∑ j, covariance (fun ω ↦ X j ω r) (fun ω ↦ X j ω s) ρ) =
        if r = s then 1 else 0) →
      (∀ j, Integrable (fun ω ↦ ‖X j ω‖ ^ 3) ρ) →
      ∀ (A : Set (ι → ℝ)), MeasurableSet A → Convex ℝ A →
        |(ρ.map (fun ω i ↦ (∑ j, X j ω) i)).real A -
          (gaussianCoordinateLaw (1 : Matrix ι ι ℝ)).real A| ≤
          (42 * (Fintype.card ι : ℝ) ^ (1 / 4 : ℝ) + 16) *
            ∑ j, ∫ ω, ‖X j ω‖ ^ 3 ∂ρ

end SRWTightness
