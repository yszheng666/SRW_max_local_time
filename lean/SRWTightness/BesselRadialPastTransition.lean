import SRWTightness.BesselPastTransitionDensity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The exact Bessel transition kernel holds on every event of the entire radial past. -/
theorem bessel_radial_past_transition (T x r t : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrt : r < t) (ht : t ≤ T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun ω ↦ f (actualBesselThree T x t ω)) (independentBridgeLaw (Fin 3))) :
    (∫ ω in {ω | (fun u : Set.Icc (0 : ℝ) r ↦ actualBesselThree T x u ω) ∈ A},
      f (actualBesselThree T x t ω) ∂independentBridgeLaw (Fin 3)) =
    ∫ ω in {ω | (fun u : Set.Icc (0 : ℝ) r ↦ actualBesselThree T x u ω) ∈ A},
      ∫ y, f y ∂besselDensityLaw (t - r) (actualBesselThree T x r ω)
        ∂independentBridgeLaw (Fin 3) := by
  let H := fun p : Fin 3 → Set.Icc (0 : ℝ) r → ℝ ↦
    fun u : Set.Icc (0 : ℝ) r ↦
      Real.sqrt (∑ i : Fin 3, ((if i = 0 then x else 0) + p i u) ^ 2)
  have hH : Measurable H := by
    apply measurable_pi_lambda
    intro u
    dsimp [H]
    fun_prop
  exact bessel_past_transition_density T x r t hT hx hr hrt ht
    (H ⁻¹' A) (hA.preimage hH) f hf hi

end SRWTightness
