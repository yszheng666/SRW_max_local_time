import SRWTightness.BesselDensitySemigroup
import SRWTightness.BesselDensityWeightedIntegrability
import SRWTightness.ActualBesselTransitionDensity
import SRWTightness.BesselThreePositiveInternal

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The original bridge density ratio is integrable under the actual Bessel path law. -/
theorem bessel_bridge_weight_integrable (T x y s : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hs : 0 < s) (hsT : s < T) :
    Integrable (fun ω ↦ besselThreeDensity (T - s) (actualBesselThree T x s ω) y /
      besselThreeDensity T x y) (independentBridgeLaw (Fin 3)) := by
  let f : ℝ → ℝ := fun z ↦ besselThreeDensity (T - s) z y / besselThreeDensity T x y
  have hf : Measurable f := by
    dsimp [f]
    unfold besselThreeDensity killedBrownianDensity
    fun_prop
  have hi : Integrable f (besselDensityLaw s x) := by
    apply (bessel_density_integrable_iff s x hs hx f).mpr
    apply ((bessel_density_product_integrable s (T - s) x y hs (sub_pos.mpr hsT) hx).div_const
      (besselThreeDensity T x y)).congr
    exact ae_of_all _ (fun z ↦ by dsimp [f]; ring)
  rw [← (actual_bessel_transition_density T x s hT hx hs hsT.le).map_eq] at hi
  exact (integrable_map_measure hf.aestronglyMeasurable
    (actualBesselThree_measurable T x s).aemeasurable).mp hi

/-- The exact bridge ratio has integral one under the actual Bessel construction. -/
theorem bessel_bridge_weight_integral_one (T x y s : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) (hsT : s < T) :
    (∫ ω, besselThreeDensity (T - s) (actualBesselThree T x s ω) y /
      besselThreeDensity T x y ∂independentBridgeLaw (Fin 3)) = 1 := by
  have hf : Measurable (fun z ↦ besselThreeDensity (T - s) z y /
      besselThreeDensity T x y) := by
    unfold besselThreeDensity killedBrownianDensity
    fun_prop
  calc
    _ = ∫ z, besselThreeDensity (T - s) z y / besselThreeDensity T x y
        ∂besselDensityLaw s x :=
      (actual_bessel_transition_density T x s hT hx hs hsT.le).integral_comp
        hf.aestronglyMeasurable
    _ = 1 := by
      rw [bessel_density_law_integral s x hs hx]
      simp_rw [← mul_div_assoc]
      rw [integral_div, bessel_density_semigroup s (T - s) x y hs (sub_pos.mpr hsT) hx,
        show s + (T - s) = T by ring,
        div_self (ne_of_gt (besselThreeDensity_pos T x y hT hx hy))]

/-- The exact Bessel bridge weighting in the original restriction input is a probability law. -/
theorem bessel_bridge_weight_probability (T x y s : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) (hsT : s < T) :
    IsProbabilityMeasure ((independentBridgeLaw (Fin 3)).withDensity
      (fun ω ↦ ENNReal.ofReal (besselThreeDensity (T - s) (actualBesselThree T x s ω) y /
        besselThreeDensity T x y))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hn : ∀ᵐ ω ∂independentBridgeLaw (Fin 3),
      0 ≤ besselThreeDensity (T - s) (actualBesselThree T x s ω) y /
        besselThreeDensity T x y := by
    filter_upwards [bessel_three_positive_input_internal T x s hT hx hs hsT.le] with ω hω
    exact (div_pos (besselThreeDensity_pos (T - s) _ y (sub_pos.mpr hsT) hω hy)
      (besselThreeDensity_pos T x y hT hx hy)).le
  rw [← ofReal_integral_eq_lintegral_ofReal
    (bessel_bridge_weight_integrable T x y s hT hx hs hsT) hn,
    bessel_bridge_weight_integral_one T x y s hT hx hy hs hsT, ENNReal.ofReal_one]

end SRWTightness
