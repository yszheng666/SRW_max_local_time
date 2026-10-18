import SRWTightness.GlobalBesselHittingMeasurable
import SRWTightness.GlobalBesselInverseMoment

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Both exact identities and the uniform bound in source (7.17)
hold for the actual global process. -/
theorem source_bessel_hitting_identity (hReflection : BridgeReflectionInput) :
    0 < besselInverseMomentConstant ∧ ∀ x b : ℝ, 0 < x → 0 < b →
      (independentBridgeLaw (Fin 3)).real
        {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω ≤ b} = min 1 (b / x) ∧
      ∀ s : ℝ, 0 < s →
        Integrable (fun ω ↦ (actualGlobalBesselThree x s ω)⁻¹) (independentBridgeLaw (Fin 3)) ∧
        (∫ ω, (actualGlobalBesselThree x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) =
          x⁻¹ * gaussianCoefficientLaw.real {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
            0 < x - Real.sqrt s * gaussianDyadicPath ω (t / s)} ∧
        (∫ ω, (actualGlobalBesselThree x s ω)⁻¹ ∂independentBridgeLaw (Fin 3)) ≤
          besselInverseMomentConstant / Real.sqrt s := by
  refine ⟨bessel_three_inverse_moment_input_internal.1, ?_⟩
  intro x b hx hb
  refine ⟨global_bessel_infinite_hitting hReflection x b hx hb, ?_⟩
  intro s hs
  exact ⟨(global_bessel_inverse_moment_bound x s hx hs).1,
    global_bessel_inverse_brownian_survival hReflection x s hx hs,
    (global_bessel_inverse_moment_bound x s hx hs).2⟩

end SRWTightness
