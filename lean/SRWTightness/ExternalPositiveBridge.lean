import SRWTightness.ExternalBridgeReflection
import SRWTightness.ExternalBesselThree
import SRWTightness.BesselThreeKernel
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual x-to-y bridge expressed in the same sign convention as the source barrier. -/
noncomputable def positiveEndpointBridge (T x y t : ℝ) (ω : GaussianCoefficientSpace) : ℝ :=
  x - endpointBrownianBridge T (x - y) t ω

/-- Conditioning on staying nonnegative, an event of positive probability for positive endpoints. -/
noncomputable def positiveBridgeCoefficientLaw (T x y : ℝ) : Measure GaussianCoefficientSpace :=
  ProbabilityTheory.cond gaussianCoefficientLaw (bridgeFlatEvent T (x - y) x)

/-- Standard bridge restriction identity, stated as equality of actual restricted path laws.
The density remains the exact kernel ratio; no uniform density bound is assumed. -/
def PositiveBridgeRestrictionInput : Prop :=
  ∀ T x y s : ℝ, 0 < T → 0 < x → 0 < y → 0 < s → s < T →
    (positiveBridgeCoefficientLaw T x y).map
      (fun ω (t : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T x y t ω) =
    ((independentBridgeLaw (Fin 3)).withDensity
      (fun ω ↦ ENNReal.ofReal (besselThreeDensity (T - s) (actualBesselThree T x s ω) y /
        besselThreeDensity T x y))).map
      (fun ω (t : Set.Icc (0 : ℝ) s) ↦ actualBesselThree T x t ω)

/-- Standard reversal of a positive bridge, with both endpoints and the full path map explicit. -/
def PositiveBridgeReversalInput : Prop :=
  ∀ T x y : ℝ, 0 < T → 0 < x → 0 < y →
    (positiveBridgeCoefficientLaw T x y).map
      (fun ω (t : Set.Icc (0 : ℝ) T) ↦ positiveEndpointBridge T x y (T - t) ω) =
    (positiveBridgeCoefficientLaw T y x).map
      (fun ω (t : Set.Icc (0 : ℝ) T) ↦ positiveEndpointBridge T y x t ω)

/-- Positivity of BES(3) at each deterministic positive time, used for kernel bounds. -/
def BesselThreePositiveInput : Prop :=
  ∀ T x s : ℝ, 0 < T → 0 < x → 0 < s → s ≤ T →
    ∀ᵐ ω ∂independentBridgeLaw (Fin 3), 0 < actualBesselThree T x s ω

/-- The source reversed distance to its flat barrier is this actual positive bridge path. -/
theorem source_reversed_positiveBridge (T q b u : ℝ) (ω : GaussianCoefficientSpace) :
    q - endpointBrownianBridge T b (T - u) ω =
      positiveEndpointBridge T q (q - b) (T - u) ω := by
  unfold positiveEndpointBridge
  congr 2
  ring

end SRWTightness
