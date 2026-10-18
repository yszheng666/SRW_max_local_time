import SRWTightness.GlobalBesselConstruction
import SRWTightness.PositiveBridgeDomination

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The global Bessel endpoint has the original actual finite-horizon endpoint law. -/
theorem global_bessel_endpoint_law (s x : ℝ) (hs : 0 < s) :
    (independentBridgeLaw (Fin 3)).map (actualGlobalBesselThree x s) =
      (independentBridgeLaw (Fin 3)).map (actualBesselThree s x s) := by
  let e : Set.Icc (0 : ℝ) s := ⟨s, hs.le, le_rfl⟩
  have hG : Measurable (fun ω (u : Set.Icc (0 : ℝ) s) ↦ actualGlobalBesselThree x u ω) :=
    measurable_pi_lambda _ (fun u ↦ actualGlobalBesselThree_measurable x u)
  have hF : Measurable (fun ω (u : Set.Icc (0 : ℝ) s) ↦ actualBesselThree s x u ω) :=
    measurable_pi_lambda _ (fun u ↦ actualBesselThree_measurable s x u)
  have he := congrArg (fun ρ : Measure (Set.Icc (0 : ℝ) s → ℝ) ↦ ρ.map (fun p ↦ p e))
    (global_bessel_finite_horizon_law s x hs)
  rw [Measure.map_map (measurable_pi_apply e) hG,
    Measure.map_map (measurable_pi_apply e) hF] at he
  exact he

/-- Every measurable global Bessel endpoint integral is its finite-horizon counterpart. -/
theorem global_bessel_endpoint_integral (s x : ℝ) (hs : 0 < s)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω, f (actualGlobalBesselThree x s ω) ∂independentBridgeLaw (Fin 3)) =
      ∫ ω, f (actualBesselThree s x s ω) ∂independentBridgeLaw (Fin 3) := by
  rw [← integral_map (actualGlobalBesselThree_measurable x s).aemeasurable
    hf.aestronglyMeasurable, global_bessel_endpoint_law s x hs,
    integral_map (actualBesselThree_measurable s x s).aemeasurable hf.aestronglyMeasurable]

end SRWTightness
