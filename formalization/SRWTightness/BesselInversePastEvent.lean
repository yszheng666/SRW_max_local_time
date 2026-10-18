import SRWTightness.BesselPast
import SRWTightness.BesselIncrementPast
import SRWTightness.BesselIncrementLaw
import SRWTightness.GaussianRadialShiftBound
import SRWTightness.IndependentParameterIntegral
import SRWTightness.BesselInverseMomentInternal
import SRWTightness.BesselThreePositiveInternal

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The inverse radial expectation decreases on every event determined by the actual vector past. -/
theorem bessel_inverse_past_event_le (T x r t : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrt : r < t) (ht : t ≤ T)
    (A : Set (Fin 3 → Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A) :
    (∫ ω in besselPast T r ⁻¹' A, (actualBesselThree T x t ω)⁻¹
      ∂independentBridgeLaw (Fin 3)) ≤
      ∫ ω in besselPast T r ⁻¹' A, (actualBesselThree T x r ω)⁻¹
        ∂independentBridgeLaw (Fin 3) := by
  let μ := independentBridgeLaw (Fin 3)
  let ν := Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 (t - r).toNNReal)
  let P := besselPast T r
  let Y := fun ω : Fin 3 → GaussianCoefficientSpace ↦ fun i ↦ Real.sqrt T *
    (gaussianDyadicPath (ω i) (t / T) - gaussianDyadicPath (ω i) (r / T))
  let F : (Fin 3 → Set.Icc (0 : ℝ) r → ℝ) × (Fin 3 → ℝ) → ℝ := fun p ↦
    (Real.sqrt (∑ i : Fin 3,
      ((if i = 0 then x else 0) + p.1 i ⟨r, hr.le, le_rfl⟩ + p.2 i) ^ 2))⁻¹
  let G := fun p ↦ ∫ y, F (p, y) ∂ν
  have hP : Measurable P := besselPast_measurable T r
  have hY : Measurable Y := by
    apply measurable_pi_lambda
    intro i
    exact measurable_const.mul
      (((gaussianDyadicPath_measurable _).comp (measurable_pi_apply i)).sub
        ((gaussianDyadicPath_measurable _).comp (measurable_pi_apply i)))
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hG : Measurable G := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hEq (ω : Fin 3 → GaussianCoefficientSpace) :
      F (P ω, Y ω) = (actualBesselThree T x t ω)⁻¹ := by
    dsimp [F, P, Y, besselPast, actualBesselThree]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ring
  have hiR := (bessel_three_inverse_moment_input_internal.2 T x r hT hx hr
    (hrt.le.trans ht)).1
  have hiT := (bessel_three_inverse_moment_input_internal.2 T x t hT hx
    (hr.trans hrt) ht).1
  have hiF : Integrable (fun ω ↦ F (P ω, Y ω)) μ := by simpa only [hEq] using hiT
  have hnonneg (p : Fin 3 → Set.Icc (0 : ℝ) r → ℝ) : 0 ≤ G p := by
    apply integral_nonneg
    intro y
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hdom : ∀ᵐ ω ∂μ, G (P ω) ≤ (actualBesselThree T x r ω)⁻¹ := by
    filter_upwards [bessel_three_positive_input_internal T x r hT hx hr
      (hrt.le.trans ht)] with ω hω
    have hnorm : 0 < ∑ i : Fin 3,
        ((if i = 0 then x else 0) + P ω i ⟨r, hr.le, le_rfl⟩) ^ 2 :=
      Real.sqrt_pos.mp hω
    exact gaussian_three_radial_shift_bound
      (fun i ↦ (if i = 0 then x else 0) + P ω i ⟨r, hr.le, le_rfl⟩)
      (t - r) (sub_pos.mpr hrt) hnorm
  have hiG : Integrable (fun ω ↦ G (P ω)) μ := by
    apply hiR.mono' (hG.comp hP).aestronglyMeasurable
    filter_upwards [hdom] with ω hω
    change ‖G (P ω)‖ ≤ _
    rw [Real.norm_of_nonneg (hnonneg _)]
    exact hω
  calc
    _ = ∫ ω in P ⁻¹' A, F (P ω, Y ω) ∂μ := by simp only [hEq]; rfl
    _ = ∫ ω in P ⁻¹' A, G (P ω) ∂μ :=
      independent_parameter_setIntegral μ ν P Y hP hY
        (bessel_vector_increment_law T r t hT hr.le hrt.le ht)
        (bessel_vector_increment_indep_past T r t hT hr.le hrt.le ht) F hF hiF A hA
    _ ≤ _ := setIntegral_mono_ae hiG.integrableOn hiR.integrableOn
      hdom

end SRWTightness
