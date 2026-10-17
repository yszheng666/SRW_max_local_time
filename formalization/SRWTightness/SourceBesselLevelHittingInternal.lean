import SRWTightness.SourceBesselLevelHittingIdentity
import SRWTightness.BridgeReflectionInternal

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Source (7.17) holds on the actual global Bessel process without a reflection hypothesis. -/
theorem source_bessel_level_hitting_identity_internal :
    0 < besselInverseMomentConstant ∧ ∀ x b : ℝ, 0 < x → 0 < b →
      (independentBridgeLaw (Fin 3)).real
        {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω = b} = min 1 (b / x) ∧
      ∀ s : ℝ, 0 < s →
        Integrable (fun ω ↦ (actualGlobalBesselThree x s ω)⁻¹) (independentBridgeLaw (Fin 3)) ∧
        (∫ ω, (actualGlobalBesselThree x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) =
          x⁻¹ * gaussianCoefficientLaw.real {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
            0 < x - Real.sqrt s * gaussianDyadicPath ω (t / s)} ∧
        (∫ ω, (actualGlobalBesselThree x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) ≤
          besselInverseMomentConstant / Real.sqrt s := by
  exact source_bessel_level_hitting_identity bridge_reflection_input_internal

end SRWTightness
