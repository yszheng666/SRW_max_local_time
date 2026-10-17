import SRWTightness.OrderedFiniteKernelUniqueness
import SRWTightness.KilledBrownianDoobRadialTransition
import SRWTightness.KilledBrownianDoobMarginal
import SRWTightness.BesselRadialPastProbability
import Mathlib.Probability.Process.FiniteDimensionalLaws

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual Doob and Bessel paths agree jointly at all positive times up to the horizon. -/
theorem killed_brownian_doob_bessel_positive_path_law (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    (killedBrownianDoobCoefficientLaw T x).map
      (fun ω (u : Set.Ioc (0 : ℝ) T) ↦ x - Real.sqrt T * gaussianDyadicPath ω (u / T)) =
    (independentBridgeLaw (Fin 3)).map
      (fun ω (u : Set.Ioc (0 : ℝ) T) ↦ actualBesselThree T x u ω) := by
  classical
  let μ := killedBrownianDoobCoefficientLaw T x
  let ν := independentBridgeLaw (Fin 3)
  let F := fun ω (u : Set.Ioc (0 : ℝ) T) ↦
    x - Real.sqrt T * gaussianDyadicPath ω (u / T)
  let G := fun ω (u : Set.Ioc (0 : ℝ) T) ↦ actualBesselThree T x u ω
  letI : IsProbabilityMeasure μ := killed_brownian_doob_probability hReflection T x hT hx
  have hF : Measurable F := measurable_pi_lambda _ (fun _ ↦
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _)))
  have hG : Measurable G := measurable_pi_lambda _ (fun _ ↦
    actualBesselThree_measurable T x _)
  have he (I : Finset (Set.Ioc (0 : ℝ) T)) :
      μ.map (fun ω ↦ I.restrict (F ω)) = ν.map (fun ω ↦ I.restrict (G ω)) := by
    apply ordered_finite_kernel_uniqueness μ ν F G hF hG
      (fun r t B z ↦ (besselDensityLaw ((t : ℝ) - r) z).real B)
      (fun r t B hB ↦ bessel_kernel_measurable ((t : ℝ) - r) B hB)
      (fun a ↦ killed_brownian_doob_bessel_marginal hReflection T x a hT hx
        a.property.1 a.property.2)
    · intro J hne a hlt A B hA hB
      let r := J.max' hne
      let H := fun p : Set.Icc (0 : ℝ) (r : ℝ) → ℝ ↦
        fun i : J ↦ p ⟨i, i.val.property.1.le, J.le_max' i.val i.property⟩
      have hH : Measurable H := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
      exact killed_brownian_doob_radial_transition hReflection T x r a hT hx
        r.property.1 (hlt r (J.max'_mem hne)) a.property.2
        (H ⁻¹' A) (hA.preimage hH) B hB
    · intro J hne a hlt A B hA hB
      let r := J.max' hne
      let H := fun p : Set.Icc (0 : ℝ) (r : ℝ) → ℝ ↦
        fun i : J ↦ p ⟨i, i.val.property.1.le, J.le_max' i.val i.property⟩
      have hH : Measurable H := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
      exact bessel_radial_past_probability T x r a hT hx
        r.property.1 (hlt r (J.max'_mem hne)) a.property.2
        (H ⁻¹' A) (hA.preimage hH) B hB
  have hμ : IsProjectiveLimit (μ.map F)
      (fun I : Finset (Set.Ioc (0 : ℝ) T) ↦ μ.map (fun ω ↦ I.restrict (F ω))) :=
    isProjectiveLimit_map hF.aemeasurable
  have hν : IsProjectiveLimit (ν.map G)
      (fun I : Finset (Set.Ioc (0 : ℝ) T) ↦ μ.map (fun ω ↦ I.restrict (F ω))) := by
    intro I
    exact (isProjectiveLimit_map hG.aemeasurable I).trans (he I).symm
  exact hμ.unique hν

end SRWTightness
