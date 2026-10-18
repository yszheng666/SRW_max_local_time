import SRWTightness.BesselBridgeWeightNormalization
import SRWTightness.BesselPastTransitionDensity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The exact bridge weights at two times agree on every event determined by the earlier past. -/
theorem bessel_bridge_weight_consistency (T x y r t : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrt : r < t) (htT : t < T)
    (A : Set (Fin 3 → Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A) :
    (∫ ω in besselPast T r ⁻¹' A,
      besselThreeDensity (T - t) (actualBesselThree T x t ω) y / besselThreeDensity T x y
        ∂independentBridgeLaw (Fin 3)) =
    ∫ ω in besselPast T r ⁻¹' A,
      besselThreeDensity (T - r) (actualBesselThree T x r ω) y / besselThreeDensity T x y
        ∂independentBridgeLaw (Fin 3) := by
  let f : ℝ → ℝ := fun z ↦ besselThreeDensity (T - t) z y / besselThreeDensity T x y
  have hf : Measurable f := by
    dsimp [f]
    unfold besselThreeDensity killedBrownianDensity
    fun_prop
  have he := bessel_past_transition_density T x r t hT hx hr hrt htT.le A hA f hf
    (bessel_bridge_weight_integrable T x y t hT hx (hr.trans hrt) htT)
  change (∫ ω in besselPast T r ⁻¹' A, f (actualBesselThree T x t ω)
    ∂independentBridgeLaw (Fin 3)) = _
  rw [he]
  apply integral_congr_ae
  apply ae_restrict_of_ae
  filter_upwards [bessel_three_positive_input_internal T x r hT hx hr
    (hrt.le.trans htT.le)] with ω hω
  rw [bessel_density_law_integral (t - r) (actualBesselThree T x r ω)
    (sub_pos.mpr hrt) hω]
  dsimp [f]
  simp_rw [← mul_div_assoc]
  rw [integral_div, bessel_density_semigroup (t - r) (T - t)
    (actualBesselThree T x r ω) y (sub_pos.mpr hrt) (sub_pos.mpr htT) hω,
    show t - r + (T - t) = T - r by ring]

end SRWTightness
