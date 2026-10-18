import SRWTightness.BesselRadialPastTransition
import SRWTightness.BesselKernelMeasurable
import SRWTightness.PositiveBridgeDomination

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Bessel endpoint events factor through the exact transition kernel on every radial-past event. -/
theorem bessel_radial_past_probability (T x r t : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrt : r < t) (ht : t ≤ T)
    (A : Set (Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (independentBridgeLaw (Fin 3)).real {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ actualBesselThree T x u ω) ∈ A ∧
      actualBesselThree T x t ω ∈ B} =
    ∫ ω in {ω | (fun u : Set.Icc (0 : ℝ) r ↦ actualBesselThree T x u ω) ∈ A},
      (besselDensityLaw (t - r) (actualBesselThree T x r ω)).real B
        ∂independentBridgeLaw (Fin 3) := by
  classical
  let μ := independentBridgeLaw (Fin 3)
  let P := fun ω (u : Set.Icc (0 : ℝ) r) ↦ actualBesselThree T x u ω
  let E := (actualBesselThree T x t) ⁻¹' B
  let f := B.indicator (fun _ ↦ (1 : ℝ))
  have hE : MeasurableSet E := hB.preimage (actualBesselThree_measurable T x t)
  have hf : Measurable f := measurable_const.indicator hB
  have hval (ω) : f (actualBesselThree T x t ω) = E.indicator (fun _ ↦ (1 : ℝ)) ω := by
    by_cases h : actualBesselThree T x t ω ∈ B <;> simp [f, E, h]
  have hi : Integrable (fun ω ↦ f (actualBesselThree T x t ω)) μ := by
    simpa only [hval] using (integrable_const (1 : ℝ)).indicator hE
  have he := bessel_radial_past_transition T x r t hT hx hr hrt ht A hA f hf hi
  have hleft : (∫ ω in P ⁻¹' A, f (actualBesselThree T x t ω) ∂μ) =
      μ.real {ω | P ω ∈ A ∧ actualBesselThree T x t ω ∈ B} := by
    simp_rw [hval]
    rw [setIntegral_indicator hE]
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rfl
  change μ.real {ω | P ω ∈ A ∧ actualBesselThree T x t ω ∈ B} = _
  rw [← hleft]
  calc
    _ = ∫ ω in P ⁻¹' A,
        ∫ y, f y ∂besselDensityLaw (t - r) (actualBesselThree T x r ω) ∂μ := he
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω ↦ integral_indicator_one hB)

end SRWTightness
