import SRWTightness.ExternalBesselThree

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The full three-coordinate Brownian past through a physical time r. -/
noncomputable def besselPast (T r : ℝ) (ω : Fin 3 → GaussianCoefficientSpace) :
    Fin 3 → Set.Icc (0 : ℝ) r → ℝ :=
  fun i u ↦ Real.sqrt T * gaussianDyadicPath (ω i) (u / T)

/-- The actual vector past is a measurable random element. -/
theorem besselPast_measurable (T r : ℝ) : Measurable (besselPast T r) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro u
  exact measurable_const.mul ((gaussianDyadicPath_measurable _).comp (measurable_pi_apply i))

/-- Recover the current positive radial coordinate from the full vector past. -/
noncomputable def besselPastRadius (x r : ℝ) (hr : 0 ≤ r)
    (p : Fin 3 → Set.Icc (0 : ℝ) r → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin 3, ((if i = 0 then x else 0) + p i ⟨r, hr, le_rfl⟩) ^ 2)

/-- The radius reconstructed from the actual past equals the actual Bessel radius. -/
theorem besselPastRadius_actual (T x r : ℝ) (hr : 0 ≤ r)
    (ω : Fin 3 → GaussianCoefficientSpace) :
    besselPastRadius x r hr (besselPast T r ω) = actualBesselThree T x r ω := rfl

/-- The radial coordinate at the end of a retained past is measurable. -/
theorem besselPastRadius_measurable (x r : ℝ) (hr : 0 ≤ r) :
    Measurable (besselPastRadius x r hr) := by
  unfold besselPastRadius
  fun_prop

end SRWTightness
