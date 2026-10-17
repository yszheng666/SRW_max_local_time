import SRWTightness.SourceBesselHittingIdentity
import SRWTightness.GlobalBesselLevelHitting

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Source (7.17), with literal level hitting
and both inverse-moment conclusions on one global path. -/
theorem source_bessel_level_hitting_identity (hReflection : BridgeReflectionInput) :
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
  obtain ⟨hC, h⟩ := source_bessel_hitting_identity hReflection
  refine ⟨hC, ?_⟩
  intro x b hx hb
  exact ⟨global_bessel_level_hitting hReflection x b hx hb, (h x b hx hb).2⟩

end SRWTightness
