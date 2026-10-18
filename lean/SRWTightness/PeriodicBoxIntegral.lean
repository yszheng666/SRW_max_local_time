import SRWTightness.PotentialFourierLaw
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory Function

namespace SRWTightness

theorem fourierInterval_integral_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ t, f t ∂fourierIntervalMeasure) = ∫ t in -Real.pi..Real.pi, f t := by
  unfold fourierIntervalMeasure
  rw [integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])]

theorem fourierInterval_integral_translate (f : ℝ → ℝ)
    (hf : Periodic f (2 * Real.pi)) (a : ℝ) :
    (∫ t, f (t + a) ∂fourierIntervalMeasure) = ∫ t, f t ∂fourierIntervalMeasure := by
  simp_rw [fourierInterval_integral_eq_intervalIntegral]
  rw [intervalIntegral.integral_comp_add_right]
  have he := hf.intervalIntegral_add_eq (-Real.pi + a) (-Real.pi)
  have h1 : -Real.pi + a + 2 * Real.pi = Real.pi + a := by ring
  have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rwa [h1, h2] at he

theorem fourierInterval_integral_double_translate (f : ℝ → ℝ)
    (hf : Periodic f (2 * Real.pi)) (hc : Continuous f) (a : ℝ) :
    (∫ t, f (2 * t + a) ∂fourierIntervalMeasure) = ∫ t, f t ∂fourierIntervalMeasure := by
  simp_rw [fourierInterval_integral_eq_intervalIntegral]
  rw [intervalIntegral.integral_comp_mul_left (fun t ↦ f (t + a)) (by norm_num : (2 : ℝ) ≠ 0),
    intervalIntegral.integral_comp_add_right]
  have he := hf.intervalIntegral_add_zsmul_eq (2 : ℤ) (2 * -Real.pi + a)
    (fun s t ↦ hc.intervalIntegrable s t)
  have h1 : 2 * -Real.pi + a + (2 : ℤ) • (2 * Real.pi) = 2 * Real.pi + a := by
    norm_num
    ring
  rw [h1, hf.intervalIntegral_add_eq (2 * -Real.pi + a) (-Real.pi)] at he
  have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [h2] at he
  rw [he]
  norm_num
  ring

end SRWTightness
