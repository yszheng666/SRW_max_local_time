import SRWTightness.TraceExitHarmonic
import SRWTightness.CompetingEntranceLaw

open MeasureTheory
namespace SRWTightness

/-- Standard strong-Markov and first-step identities for actual finite-domain exit kernels.
The input contains no geometric approximation or relative comparison estimate. -/
def KilledExitDecompositionInput : Prop :=
  (∀ (D K : Finset Site), K ⊆ D → ∀ x e : Site, e ∉ D →
    traceExitProbability D x e = traceExitProbability (D \ K) x e +
      ∫ y, traceExitProbability D y e ∂competingEntranceLaw D K x) ∧
  (∀ (D K : Finset Site), K ⊆ D → ∀ x ∈ K,
    traceStopProbability D K x =
      (1 / 4 : ℝ) * ∑ d : Direction, competingExitMass D K (x + step d)) ∧
  (∀ (D K : Finset Site), K ⊆ D → ∀ x ∈ K, ∀ e : Site, e ∉ D →
    traceStopExitProbability D K x e =
      (1 / 4 : ℝ) * ∑ d : Direction, traceExitProbability (D \ K) (x + step d) e)

end SRWTightness
