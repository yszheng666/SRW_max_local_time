import SRWTightness.PotentialFourierLaw
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

namespace SRWTightness

theorem fourierInterval_integral_cos (n : ℤ) :
    (∫ t, Real.cos ((n : ℝ) * t) ∂fourierIntervalMeasure) = if n = 0 then 2 * Real.pi else 0 := by
  unfold fourierIntervalMeasure
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])]
  by_cases hn : n = 0
  · subst n
    simp
    ring
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [if_neg hn, intervalIntegral.integral_comp_mul_left Real.cos hn', integral_cos]
    simp [mul_neg, Real.sin_neg, Real.sin_int_mul_pi]

theorem fourierInterval_integral_sin (n : ℤ) :
    (∫ t, Real.sin ((n : ℝ) * t) ∂fourierIntervalMeasure) = 0 := by
  unfold fourierIntervalMeasure
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])]
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [intervalIntegral.integral_comp_mul_left Real.sin hn', integral_sin]
    simp [mul_neg, Real.cos_neg]

theorem fourierInterval_integrable_cos (n : ℤ) :
    Integrable (fun t ↦ Real.cos ((n : ℝ) * t)) fourierIntervalMeasure := by
  have hm : Measurable (fun t : ℝ ↦ Real.cos ((n : ℝ) * t)) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t ↦ by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)

theorem fourierInterval_integrable_sin (n : ℤ) :
    Integrable (fun t ↦ Real.sin ((n : ℝ) * t)) fourierIntervalMeasure := by
  have hm : Measurable (fun t : ℝ ↦ Real.sin ((n : ℝ) * t)) := by fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t ↦ by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one _)

theorem fourierBox_integral_cos_phase (z : Site) :
    (∫ θ, Real.cos (fourierPhase z θ) ∂fourierBoxMeasure) =
      if z = 0 then 4 * Real.pi ^ 2 else 0 := by
  unfold fourierPhase fourierBoxMeasure
  simp_rw [Real.cos_add]
  rw [integral_sub ((fourierInterval_integrable_cos z.1).mul_prod (fourierInterval_integrable_cos z.2))
    ((fourierInterval_integrable_sin z.1).mul_prod (fourierInterval_integrable_sin z.2)),
    integral_prod_mul (fun t : ℝ ↦ Real.cos ((z.1 : ℝ) * t)) (fun t : ℝ ↦ Real.cos ((z.2 : ℝ) * t)),
    integral_prod_mul (fun t : ℝ ↦ Real.sin ((z.1 : ℝ) * t)) (fun t : ℝ ↦ Real.sin ((z.2 : ℝ) * t)),
    fourierInterval_integral_cos, fourierInterval_integral_cos,
    fourierInterval_integral_sin, fourierInterval_integral_sin]
  by_cases hx : z.1 = 0 <;> by_cases hy : z.2 = 0 <;>
    simp [hx, hy, Prod.ext_iff] <;> ring

end SRWTightness
