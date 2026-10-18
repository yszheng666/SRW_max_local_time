import SRWTightness.KilledBrownianDoobLaw
import SRWTightness.ScaledGaussianStrictSurvivalMeasurable
import SRWTightness.RestrictedDensityEventReal

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Events under the actual Doob law are terminal-distance integrals on strictly surviving paths. -/
theorem killed_brownian_doob_event_real (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x)
    (B : Set GaussianCoefficientSpace) (hB : MeasurableSet B) :
    (killedBrownianDoobCoefficientLaw T x).real B =
      ∫ ω in {ω | (∀ t ∈ Set.Icc (0 : ℝ) T,
        0 < x - Real.sqrt T * gaussianDyadicPath ω (t / T)) ∧ ω ∈ B},
        (x - Real.sqrt T * gaussianDyadicPath ω (T / T)) / x ∂gaussianCoefficientLaw := by
  have hw : Measurable (fun ω ↦
      (x - Real.sqrt T * gaussianDyadicPath ω (T / T)) / x) :=
    (measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _))).div_const x
  exact restricted_density_event_real gaussianCoefficientLaw _
    (scaled_gaussian_strict_survival_nullMeasurable hReflection T x hT hx) _ hw
    (fun ω hω ↦ div_nonneg (hω T ⟨hT.le, le_rfl⟩).le hx.le) B hB

end SRWTightness
