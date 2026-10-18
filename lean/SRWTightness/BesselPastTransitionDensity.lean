import SRWTightness.GaussianShiftedRadialDensity
import SRWTightness.BesselInversePastEvent

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- On every vector-past event, the actual radial future has the literal Bessel
transition kernel. -/
theorem bessel_past_transition_density (T x r t : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hr : 0 < r) (hrt : r < t) (ht : t ≤ T)
    (A : Set (Fin 3 → Set.Icc (0 : ℝ) r → ℝ)) (hA : MeasurableSet A)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun ω ↦ f (actualBesselThree T x t ω)) (independentBridgeLaw (Fin 3))) :
    (∫ ω in besselPast T r ⁻¹' A, f (actualBesselThree T x t ω)
      ∂independentBridgeLaw (Fin 3)) =
      ∫ ω in besselPast T r ⁻¹' A,
        ∫ y, f y ∂besselDensityLaw (t - r) (actualBesselThree T x r ω)
          ∂independentBridgeLaw (Fin 3) := by
  let μ := independentBridgeLaw (Fin 3)
  let ν := Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 (t - r).toNNReal)
  let P := besselPast T r
  let Y := fun ω : Fin 3 → GaussianCoefficientSpace ↦ fun i ↦ Real.sqrt T *
    (gaussianDyadicPath (ω i) (t / T) - gaussianDyadicPath (ω i) (r / T))
  let F : (Fin 3 → Set.Icc (0 : ℝ) r → ℝ) × (Fin 3 → ℝ) → ℝ := fun p ↦
    f (Real.sqrt (∑ i : Fin 3,
      ((if i = 0 then x else 0) + p.1 i ⟨r, hr.le, le_rfl⟩ + p.2 i) ^ 2))
  let G := fun p ↦ ∫ y, F (p, y) ∂ν
  have hP : Measurable P := besselPast_measurable T r
  have hY : Measurable Y := by
    apply measurable_pi_lambda
    intro i
    exact measurable_const.mul
      (((gaussianDyadicPath_measurable _).comp (measurable_pi_apply i)).sub
        ((gaussianDyadicPath_measurable _).comp (measurable_pi_apply i)))
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hEq (ω : Fin 3 → GaussianCoefficientSpace) :
      F (P ω, Y ω) = f (actualBesselThree T x t ω) := by
    dsimp [F, P, Y, besselPast, actualBesselThree]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ring
  have hiF : Integrable (fun ω ↦ F (P ω, Y ω)) μ := by simpa only [hEq] using hi
  have hinner : ∀ᵐ ω ∂μ,
      G (P ω) = ∫ y, f y ∂besselDensityLaw (t - r) (actualBesselThree T x r ω) := by
    filter_upwards [bessel_three_positive_input_internal T x r hT hx hr
      (hrt.le.trans ht)] with ω hω
    have hnorm : 0 < ∑ i : Fin 3,
        ((if i = 0 then x else 0) + P ω i ⟨r, hr.le, le_rfl⟩) ^ 2 :=
      Real.sqrt_pos.mp hω
    exact (gaussian_shifted_radial_density
      (fun i ↦ (if i = 0 then x else 0) + P ω i ⟨r, hr.le, le_rfl⟩)
      (t - r) (sub_pos.mpr hrt) hnorm).integral_comp hf.aestronglyMeasurable
  calc
    _ = ∫ ω in P ⁻¹' A, F (P ω, Y ω) ∂μ := by simp only [hEq]; rfl
    _ = ∫ ω in P ⁻¹' A, G (P ω) ∂μ :=
      independent_parameter_setIntegral μ ν P Y hP hY
        (bessel_vector_increment_law T r t hT hr.le hrt.le ht)
        (bessel_vector_increment_indep_past T r t hT hr.le hrt.le ht) F hF hiF A hA
    _ = _ := integral_congr_ae (ae_restrict_of_ae hinner)

end SRWTightness
