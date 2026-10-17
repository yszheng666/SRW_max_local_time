import Mathlib.Probability.Moments.Tilted
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Exact inverse-tilt integral on an event. -/
theorem inverse_tilt_event_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Integrable (fun ω ↦ Real.exp (X ω)) μ) (E : Set Ω) (hE : MeasurableSet E) :
    (∫ ω in E, Real.exp (cgf X μ 1 - X ω) ∂μ.tilted X) = μ.real E := by
  have hh := setIntegral_tilted_mul_eq_cgf'
    (μ := μ) (X := X) (t := 1) (fun ω ↦ Real.exp (cgf X μ 1 - X ω)) hE
    (by simpa using hX)
  simpa only [one_mul, smul_eq_mul, ← Real.exp_add, sub_add_sub_cancel, sub_self, Real.exp_zero,
    integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] using hh

/-- The inverse density is integrable under the tilted probability law. -/
theorem inverse_tilt_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Integrable (fun ω ↦ Real.exp (X ω)) μ) :
    Integrable (fun ω ↦ Real.exp (cgf X μ 1 - X ω)) (μ.tilted X) := by
  apply (integrable_tilted_iff hX _).mpr
  have he (ω : Ω) : Real.exp (X ω) * Real.exp (cgf X μ 1 - X ω) =
      Real.exp (cgf X μ 1) := by rw [← Real.exp_add]; congr 1; ring
  simpa only [smul_eq_mul, he] using
    (integrable_const (Real.exp (cgf X μ 1)) : Integrable (fun _ : Ω ↦ Real.exp (cgf X μ 1)) μ)

/-- Uniform inverse-density bounds transfer the actual tilted event probability. -/
theorem inverse_tilt_event_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Integrable (fun ω ↦ Real.exp (X ω)) μ) (E : Set Ω) (hE : MeasurableSet E)
    (L U : ℝ) (hL : ∀ ω ∈ E, L ≤ Real.exp (cgf X μ 1 - X ω))
    (hU : ∀ ω ∈ E, Real.exp (cgf X μ 1 - X ω) ≤ U) :
    L * (μ.tilted X).real E ≤ μ.real E ∧ μ.real E ≤ U * (μ.tilted X).real E := by
  letI := isProbabilityMeasure_tilted hX
  have hi := (inverse_tilt_integrable μ X hX).integrableOn (s := E)
  have hlo := integral_mono_ae (integrable_const L) hi
    ((ae_restrict_iff' hE).mpr (ae_of_all _ hL))
  have hup := integral_mono_ae hi (integrable_const U)
    ((ae_restrict_iff' hE).mpr (ae_of_all _ hU))
  rw [inverse_tilt_event_integral μ X hX E hE] at hlo hup
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm] using
    And.intro hlo hup

end SRWTightness
