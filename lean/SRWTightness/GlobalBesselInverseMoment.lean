import SRWTightness.GlobalBesselMarginal
import SRWTightness.BesselInverseBrownianSurvival
import SRWTightness.BesselInverseMomentInternal

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The global Bessel inverse moment is the original Brownian survival probability divided by x. -/
theorem global_bessel_inverse_brownian_survival (hReflection : BridgeReflectionInput)
    (x s : ℝ) (hx : 0 < x) (hs : 0 < s) :
    (∫ ω, (actualGlobalBesselThree x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) =
      x⁻¹ * gaussianCoefficientLaw.real
        {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
          0 < x - Real.sqrt s * gaussianDyadicPath ω (t / s)} := by
  rw [global_bessel_endpoint_integral s x hs (fun z ↦ z⁻¹) measurable_inv]
  exact bessel_inverse_brownian_survival hReflection s x s hs hx hs le_rfl

/-- The global Bessel inverse radius is integrable and satisfies the same universal decay bound. -/
theorem global_bessel_inverse_moment_bound (x s : ℝ) (hx : 0 < x) (hs : 0 < s) :
    Integrable (fun ω ↦ (actualGlobalBesselThree x s ω)⁻¹) (independentBridgeLaw (Fin 3)) ∧
    (∫ ω, (actualGlobalBesselThree x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) ≤
      besselInverseMomentConstant / Real.sqrt s := by
  have hi := bessel_three_inverse_moment_input_internal.2 s x s hs hx hs le_rfl
  constructor
  · apply (integrable_map_measure measurable_inv.aestronglyMeasurable
      (actualGlobalBesselThree_measurable x s).aemeasurable).mp
    rw [global_bessel_endpoint_law s x hs]
    exact (integrable_map_measure measurable_inv.aestronglyMeasurable
      (actualBesselThree_measurable s x s).aemeasurable).mpr hi.1
  · rw [global_bessel_endpoint_integral s x hs (fun z ↦ z⁻¹) measurable_inv]
    exact hi.2

end SRWTightness
