import SRWTightness.PeriodicBoxIntegral
import SRWTightness.FourierBoxOrthogonality

open MeasureTheory

namespace SRWTightness

noncomputable def cosineMoment (n : ℕ) (k : ℤ) : ℝ :=
  ∫ t, Real.cos t ^ n * Real.cos ((k : ℝ) * t) ∂fourierIntervalMeasure

noncomputable def sineMoment (n : ℕ) (k : ℤ) : ℝ :=
  ∫ t, Real.cos t ^ n * Real.sin ((k : ℝ) * t) ∂fourierIntervalMeasure

theorem integrable_cosineMoment (n : ℕ) (k : ℤ) :
    Integrable (fun t ↦ Real.cos t ^ n * Real.cos ((k : ℝ) * t)) fourierIntervalMeasure :=
  (show Continuous (fun t : ℝ ↦ Real.cos t ^ n * Real.cos ((k : ℝ) * t)) by fun_prop).integrableOn_Icc

theorem integrable_sineMoment (n : ℕ) (k : ℤ) :
    Integrable (fun t ↦ Real.cos t ^ n * Real.sin ((k : ℝ) * t)) fourierIntervalMeasure :=
  (show Continuous (fun t : ℝ ↦ Real.cos t ^ n * Real.sin ((k : ℝ) * t)) by fun_prop).integrableOn_Icc

theorem fourierInterval_integral_neg (f : ℝ → ℝ) :
    (∫ t, f (-t) ∂fourierIntervalMeasure) = ∫ t, f t ∂fourierIntervalMeasure := by
  simp_rw [fourierInterval_integral_eq_intervalIntegral]
  rw [intervalIntegral.integral_comp_neg]
  simp

theorem sineMoment_eq_zero (n : ℕ) (k : ℤ) : sineMoment n k = 0 := by
  have he := fourierInterval_integral_neg (fun t ↦ Real.cos t ^ n * Real.sin ((k : ℝ) * t))
  simp only [Real.cos_neg, mul_neg, Real.sin_neg] at he
  rw [integral_neg] at he
  change -sineMoment n k = sineMoment n k at he
  linarith

theorem cosineMoment_zero (k : ℤ) : cosineMoment 0 k = if k = 0 then 2 * Real.pi else 0 := by
  simpa only [cosineMoment, pow_zero, one_mul] using fourierInterval_integral_cos k

end SRWTightness
