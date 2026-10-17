import SRWTightness.ScaledGaussianKilledStrictProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual Brownian path killed at zero has the manuscript's transition density. -/
theorem actual_killed_brownian_transition_density (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    (gaussianCoefficientLaw.restrict
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
        0 < x - Real.sqrt T * gaussianDyadicPath ω (t / T)}).map
      (fun ω ↦ x - Real.sqrt T * gaussianDyadicPath ω (T / T)) =
      killedBrownianDensityLaw T x := by
  letI := killed_brownian_density_law_finite T x hT hx
  have hm : Measurable (fun ω ↦ x - Real.sqrt T * gaussianDyadicPath ω (T / T)) :=
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _))
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hm hA, Measure.restrict_apply (hA.preimage hm)]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact scaled_gaussian_killed_strict_probability hReflection T x hT hx A hA

end SRWTightness
