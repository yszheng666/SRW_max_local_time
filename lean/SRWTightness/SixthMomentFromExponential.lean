import SRWTightness.NaturalExponentialMoment

open MeasureTheory

namespace SRWTightness

theorem pow_six_le_exp_sub_one (x : ℝ) (hx : 0 ≤ x) :
    x ^ 6 ≤ 720 * (Real.exp x - 1) := by
  have hh := Real.sum_le_exp_of_nonneg hx 7
  norm_num [Finset.sum_range_succ] at hh
  linarith [pow_nonneg hx 2, pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5]

/-- Subtracting the constant term in the exponential moment saves one power of the scale. -/
theorem sixth_moment_of_exponential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (s C : ℝ) (hs : 0 < s)
    (hi : Integrable (fun ω ↦ Real.exp (s * X ω)) μ)
    (hb : (∫ ω, Real.exp (s * X ω) ∂μ) ≤ 1 + C * s) :
    Integrable (fun ω ↦ X ω ^ 6) μ ∧
    (∫ ω, X ω ^ 6 ∂μ) ≤ 720 * C / s ^ 5 := by
  have hdom (ω : Ω) : X ω ^ 6 ≤ (720 / s ^ 6) * (Real.exp (s * X ω) - 1) := by
    have hh := pow_six_le_exp_sub_one (s * X ω) (mul_nonneg hs.le (hX0 ω))
    rw [mul_pow] at hh
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hs 6)).mpr
    nlinarith
  have hiB : Integrable (fun ω ↦ (720 / s ^ 6) * (Real.exp (s * X ω) - 1)) μ :=
    (hi.sub (integrable_const 1)).const_mul _
  have hiX : Integrable (fun ω ↦ X ω ^ 6) μ := hiB.mono'
    (hX.pow_const 6).aestronglyMeasurable (Filter.Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hX0 ω) 6)]
      exact hdom ω))
  refine ⟨hiX, ?_⟩
  have hh := integral_mono hiX hiB hdom
  rw [integral_const_mul, integral_sub hi (integrable_const 1), integral_const] at hh
  simp only [probReal_univ, smul_eq_mul, one_mul] at hh
  calc
    _ ≤ (720 / s ^ 6) * ((∫ ω, Real.exp (s * X ω) ∂μ) - 1) := hh
    _ ≤ (720 / s ^ 6) * (C * s) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by field_simp <;> ring

end SRWTightness
