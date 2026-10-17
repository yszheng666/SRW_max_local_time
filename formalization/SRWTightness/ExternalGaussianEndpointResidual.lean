import SRWTightness.SourcePairObservationCovariance
import SRWTightness.PairResidualDensity
import SRWTightness.GaussianMeanLaw

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Standard finite Gaussian endpoint-plus-independent-residual construction.
This is a supplied foundational input, not a proved fact of this project. -/
def GaussianEndpointResidualInput : Prop :=
  ∀ (n : ℕ) (last : Fin n) (T : Fin n → ℝ) (V : Matrix Bool Bool ℝ),
    (∀ j, T j ≤ T last) → V true false = V false true →
    (∀ x : Fin n → ℝ, 0 ≤ ∑ j, ∑ l, x j * min (T j) (T l) * x l) →
    (pairResidualMatrix (V false false) (V true true) (V false true) (T last)).PosDef →
    gaussianCoordinateLaw (pairObservationCovarianceMatrix T (fun _ ↦ 0) V) =
      ((gaussianCoordinateLaw (fun j l ↦ min (T j) (T l))).prod
        (gaussianCoordinateLaw
          (pairResidualMatrix (V false false) (V true true) (V false true) (T last)))).map
        (fun p j ↦ match j with
          | Sum.inl a => p.1 a
          | Sum.inr c => p.1 last + p.2 (if c then 1 else 0))

end SRWTightness
