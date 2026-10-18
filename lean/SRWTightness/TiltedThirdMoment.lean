import SRWTightness.SixthMomentFromExponential
import Mathlib.MeasureTheory.Measure.Tilted

open MeasureTheory

namespace SRWTightness

/-- A sixth moment and a doubled exponential moment control the third moment after tilting. -/
theorem tilted_third_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X f : Ω → ℝ)
    (hX : Measurable X) (hf : Measurable f) (hX0 : ∀ ω, 0 ≤ X ω)
    (L M : ℝ) (hL : 0 < L)
    (hi6 : Integrable (fun ω ↦ X ω ^ 6) μ)
    (hb6 : (∫ ω, X ω ^ 6 ∂μ) ≤ M * L ^ 6)
    (hiE : Integrable (fun ω ↦ Real.exp (f ω)) μ)
    (hZ : 1 / 2 ≤ ∫ ω, Real.exp (f ω) ∂μ)
    (hi2 : Integrable (fun ω ↦ Real.exp (2 * f ω)) μ)
    (hb2 : (∫ ω, Real.exp (2 * f ω) ∂μ) ≤ 2) :
    Integrable (fun ω ↦ X ω ^ 3) (μ.tilted f) ∧
    (∫ ω, X ω ^ 3 ∂μ.tilted f) ≤ (M + 2) * L ^ 3 := by
  have hdom (ω : Ω) : X ω ^ 3 * Real.exp (f ω) ≤
      (X ω ^ 6 + L ^ 6 * Real.exp (2 * f ω)) / (2 * L ^ 3) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have he : Real.exp (2 * f ω) = Real.exp (f ω) ^ 2 := by
      rw [two_mul, Real.exp_add, pow_two]
    rw [he]
    nlinarith [sq_nonneg (X ω ^ 3 - L ^ 3 * Real.exp (f ω))]
  have hiB : Integrable (fun ω ↦ (X ω ^ 6 + L ^ 6 * Real.exp (2 * f ω)) / (2 * L ^ 3)) μ :=
    (hi6.add (hi2.const_mul (L ^ 6))).div_const _
  have hm : Measurable (fun ω ↦ X ω ^ 3 * Real.exp (f ω)) := by fun_prop
  have hiP : Integrable (fun ω ↦ X ω ^ 3 * Real.exp (f ω)) μ :=
    hiB.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (hX0 ω) 3) (Real.exp_pos _).le)]
      exact hdom ω))
  have hiT : Integrable (fun ω ↦ X ω ^ 3) (μ.tilted f) :=
    (integrable_tilted_iff hiE _).mpr (by simpa only [smul_eq_mul, mul_comm] using hiP)
  have hb := integral_mono hiP hiB hdom
  rw [integral_div, integral_add hi6 (hi2.const_mul (L ^ 6)), integral_const_mul] at hb
  have hN : (∫ ω, X ω ^ 3 * Real.exp (f ω) ∂μ) ≤ ((M + 2) / 2) * L ^ 3 := by
    calc
      _ ≤ ((∫ ω, X ω ^ 6 ∂μ) + L ^ 6 * (∫ ω, Real.exp (2 * f ω) ∂μ)) / (2 * L ^ 3) := hb
      _ ≤ (M * L ^ 6 + L ^ 6 * 2) / (2 * L ^ 3) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact add_le_add hb6 (mul_le_mul_of_nonneg_left hb2 (by positivity))
      _ = _ := by field_simp <;> ring
  have hN0 : 0 ≤ ∫ ω, X ω ^ 3 * Real.exp (f ω) ∂μ :=
    integral_nonneg (fun ω ↦ mul_nonneg (pow_nonneg (hX0 ω) 3) (Real.exp_pos _).le)
  have hZ0 : 0 < ∫ ω, Real.exp (f ω) ∂μ := by linarith
  have hratio : (∫ ω, X ω ^ 3 * Real.exp (f ω) ∂μ) / (∫ ω, Real.exp (f ω) ∂μ) ≤
      2 * (∫ ω, X ω ^ 3 * Real.exp (f ω) ∂μ) := by
    apply (div_le_iff₀ hZ0).mpr
    nlinarith [mul_nonneg hN0 (show 0 ≤ (∫ ω, Real.exp (f ω) ∂μ) - 1 / 2 by linarith)]
  refine ⟨hiT, ?_⟩
  rw [integral_tilted]
  have heq : (fun ω ↦ (Real.exp (f ω) / (∫ a, Real.exp (f a) ∂μ)) • X ω ^ 3) =
      (fun ω ↦ (X ω ^ 3 * Real.exp (f ω)) / (∫ a, Real.exp (f a) ∂μ)) := by
    funext ω
    simp only [smul_eq_mul]
    ring
  rw [heq, integral_div]
  linarith

end SRWTightness
