import SRWTightness.BesselPast
import SRWTightness.ScaledGaussianPrefixLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The whole vector Brownian past has the same law under a shorter construction horizon. -/
theorem bessel_vector_prefix_law (T r : ℝ) (hT : 0 < T) (hr : 0 < r) (hrT : r ≤ T) :
    (independentBridgeLaw (Fin 3)).map (besselPast T r) =
      (independentBridgeLaw (Fin 3)).map (besselPast r r) := by
  have hm (S : ℝ) : Measurable (fun ω (u : Set.Icc (0 : ℝ) r) ↦
      Real.sqrt S * gaussianDyadicPath ω (u / S)) :=
    measurable_pi_lambda _ (fun _ ↦ measurable_const.mul (gaussianDyadicPath_measurable _))
  have hp (S : ℝ) : (independentBridgeLaw (Fin 3)).map (besselPast S r) =
      Measure.pi (fun _ : Fin 3 ↦ gaussianCoefficientLaw.map
        (fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt S * gaussianDyadicPath ω (u / S))) := by
    rw [independentBridgeLaw, Measure.infinitePi_eq_pi]
    exact Measure.pi_map_pi (μ := fun _ : Fin 3 ↦ gaussianCoefficientLaw)
      (fun _ ↦ (hm S).aemeasurable)
  rw [hp T, hp r]
  congr 1
  funext i
  exact scaled_gaussian_prefix_law T r hT hr hrT

/-- The entire radial prefix has the exact Bessel path law constructed for that shorter duration. -/
theorem bessel_radial_prefix_law (T x r : ℝ) (hT : 0 < T) (hr : 0 < r) (hrT : r ≤ T) :
    (independentBridgeLaw (Fin 3)).map
      (fun ω (u : Set.Icc (0 : ℝ) r) ↦ actualBesselThree T x u ω) =
    (independentBridgeLaw (Fin 3)).map
      (fun ω (u : Set.Icc (0 : ℝ) r) ↦ actualBesselThree r x u ω) := by
  let H := fun p : Fin 3 → Set.Icc (0 : ℝ) r → ℝ ↦
    fun u : Set.Icc (0 : ℝ) r ↦
      Real.sqrt (∑ i : Fin 3, ((if i = 0 then x else 0) + p i u) ^ 2)
  have hH : Measurable H := by
    apply measurable_pi_lambda
    intro u
    dsimp [H]
    fun_prop
  have he := congrArg (fun ν : Measure (Fin 3 → Set.Icc (0 : ℝ) r → ℝ) ↦ ν.map H)
    (bessel_vector_prefix_law T r hT hr hrT)
  rw [Measure.map_map hH (besselPast_measurable T r),
    Measure.map_map hH (besselPast_measurable r r)] at he
  exact he

end SRWTightness
