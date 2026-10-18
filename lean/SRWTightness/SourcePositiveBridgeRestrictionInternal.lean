import SRWTightness.ActualKilledBrownianDensity
import SRWTightness.PositiveBridgeRestrictionInternal
import SRWTightness.BridgeReflectionInternal

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual killed Brownian transition law has the explicit density without a
reflection input. -/
theorem actual_killed_brownian_transition_density_internal
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    (gaussianCoefficientLaw.restrict
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
        0 < x - Real.sqrt T * gaussianDyadicPath ω (t / T)}).map
      (fun ω ↦ x - Real.sqrt T * gaussianDyadicPath ω (T / T)) =
      killedBrownianDensityLaw T x := by
  exact actual_killed_brownian_transition_density bridge_reflection_input_internal T x hT hx

/-- The complete original positive-bridge restriction input holds without literature hypotheses. -/
theorem positive_bridge_restriction_input_unconditional : PositiveBridgeRestrictionInput := by
  exact positive_bridge_restriction_input_internal bridge_reflection_input_internal

end SRWTightness
