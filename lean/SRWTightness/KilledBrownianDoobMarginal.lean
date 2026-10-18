import SRWTightness.KilledBrownianDoobPrefixConsistency
import SRWTightness.ActualBesselTransitionDensity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Every positive-time marginal of the actual Doob path has the exact Bessel density. -/
theorem killed_brownian_doob_marginal (hReflection : BridgeReflectionInput)
    (T x t : ℝ) (hT : 0 < T) (hx : 0 < x) (ht : 0 < t) (htT : t ≤ T) :
    (killedBrownianDoobCoefficientLaw T x).map
      (fun ω ↦ x - Real.sqrt T * gaussianDyadicPath ω (t / T)) = besselDensityLaw t x := by
  rcases eq_or_lt_of_le htT with h | h
  · subst t
    exact killed_brownian_doob_endpoint_law hReflection T x hT hx
  · let H := fun p : Set.Icc (0 : ℝ) t → ℝ ↦ x - p ⟨t, ht.le, le_rfl⟩
    have hH : Measurable H := measurable_const.sub (measurable_pi_apply _)
    have hm (S : ℝ) : Measurable (fun ω (u : Set.Icc (0 : ℝ) t) ↦
        Real.sqrt S * gaussianDyadicPath ω (u / S)) :=
      measurable_pi_lambda _ (fun _ ↦ measurable_const.mul (gaussianDyadicPath_measurable _))
    have he := congrArg (fun μ : Measure (Set.Icc (0 : ℝ) t → ℝ) ↦ μ.map H)
      (killed_brownian_doob_prefix_consistency hReflection T x t hT hx ht h)
    rw [Measure.map_map hH (hm T), Measure.map_map hH (hm t)] at he
    exact he.trans (killed_brownian_doob_endpoint_law hReflection t x ht hx)

/-- The actual Doob and actual Bessel processes agree at every deterministic positive time. -/
theorem killed_brownian_doob_bessel_marginal (hReflection : BridgeReflectionInput)
    (T x t : ℝ) (hT : 0 < T) (hx : 0 < x) (ht : 0 < t) (htT : t ≤ T) :
    (killedBrownianDoobCoefficientLaw T x).map
      (fun ω ↦ x - Real.sqrt T * gaussianDyadicPath ω (t / T)) =
    (independentBridgeLaw (Fin 3)).map (actualBesselThree T x t) := by
  rw [killed_brownian_doob_marginal hReflection T x t hT hx ht htT,
    (actual_bessel_transition_density T x t hT hx ht htT).map_eq]

end SRWTightness
