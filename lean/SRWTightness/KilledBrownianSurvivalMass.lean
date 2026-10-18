import SRWTightness.ActualKilledBrownianDensity
import SRWTightness.ScaledGaussianStrictFlatProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The total killed-kernel mass is the exact Brownian survival Gaussian interval probability. -/
theorem killed_brownian_survival_mass (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    (killedBrownianDensityLaw T x).real Set.univ =
      (gaussianReal 0 T.toNNReal).real (Set.Icc (-x) x) := by
  have hm : Measurable (fun ω ↦ x - Real.sqrt T * gaussianDyadicPath ω (T / T)) :=
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _))
  rw [← actual_killed_brownian_transition_density hReflection T x hT hx,
    map_measureReal_apply hm MeasurableSet.univ, Set.preimage_univ]
  simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  simpa only [sub_pos, Measure.real] using
    scaled_gaussian_strict_flat_probability hReflection T x hT hx

end SRWTightness
