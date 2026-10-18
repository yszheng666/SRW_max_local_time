import SRWTightness.ActualKilledBrownianDensity
import SRWTightness.BesselKilledDensityTransform
import SRWTightness.DensityMapPullback

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Actual Brownian coefficients restricted to strict positive survival and weighted linearly. -/
noncomputable def killedBrownianDoobCoefficientLaw (T x : ℝ) : Measure GaussianCoefficientSpace :=
  (gaussianCoefficientLaw.restrict
    {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
      0 < x - Real.sqrt T * gaussianDyadicPath ω (t / T)}).withDensity
    (fun ω ↦ ENNReal.ofReal ((x - Real.sqrt T * gaussianDyadicPath ω (T / T)) / x))

/-- The actual linearly weighted killed Brownian endpoint has the Bessel transition law. -/
theorem killed_brownian_doob_endpoint_law (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    (killedBrownianDoobCoefficientLaw T x).map
      (fun ω ↦ x - Real.sqrt T * gaussianDyadicPath ω (T / T)) = besselDensityLaw T x := by
  have hm : Measurable (fun ω ↦ x - Real.sqrt T * gaussianDyadicPath ω (T / T)) :=
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _))
  unfold killedBrownianDoobCoefficientLaw
  rw [density_map_pullback _ _ hm (fun y : ℝ ↦ ENNReal.ofReal (y / x))
    (by fun_prop), actual_killed_brownian_transition_density hReflection T x hT hx,
    ← bessel_killed_density_transform T x hT hx]

/-- Linear weighting of the actual strictly surviving Brownian path is a probability law. -/
theorem killed_brownian_doob_probability (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    IsProbabilityMeasure (killedBrownianDoobCoefficientLaw T x) := by
  letI := bessel_density_law_probability T x hT hx
  have hm : Measurable (fun ω ↦ x - Real.sqrt T * gaussianDyadicPath ω (T / T)) :=
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _))
  have he := congrArg (fun μ : Measure ℝ ↦ μ Set.univ)
    (killed_brownian_doob_endpoint_law hReflection T x hT hx)
  rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
    measure_univ (μ := besselDensityLaw T x)] at he
  exact ⟨he⟩

end SRWTightness
