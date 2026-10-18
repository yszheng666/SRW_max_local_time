import SRWTightness.PeriodicBoxRotation
import SRWTightness.FourierCosineMoments
import SRWTightness.SRWFourierInversion

open MeasureTheory Function

namespace SRWTightness

theorem fourierCharacteristic_rotate (u v : ℝ) :
    fourierCharacteristic (u + v, u - v) = Real.cos u * Real.cos v := by
  simp only [fourierCharacteristic, Real.cos_add, Real.cos_sub]
  ring

theorem fourierPhase_rotate (z : Site) (u v : ℝ) :
    fourierPhase z (u + v, u - v) = ((z.1 + z.2 : ℤ) : ℝ) * u + ((z.1 - z.2 : ℤ) : ℝ) * v := by
  simp only [fourierPhase, Int.cast_add, Int.cast_sub]
  ring

theorem fourierTransition_periodic_fst (n : ℕ) (z : Site) (y : ℝ) :
    Periodic (fun x ↦ fourierCharacteristic (x, y) ^ n * Real.cos (fourierPhase z (x, y))) (2 * Real.pi) := by
  intro x
  have hp : fourierPhase z (x + 2 * Real.pi, y) = fourierPhase z (x, y) + (z.1 : ℝ) * (2 * Real.pi) := by
    simp only [fourierPhase]
    ring
  dsimp only
  rw [hp, Real.cos_add_int_mul_two_pi]
  simp only [fourierCharacteristic, Real.cos_add_two_pi]

theorem fourierTransition_periodic_snd (n : ℕ) (z : Site) (x : ℝ) :
    Periodic (fun y ↦ fourierCharacteristic (x, y) ^ n * Real.cos (fourierPhase z (x, y))) (2 * Real.pi) := by
  intro y
  have hp : fourierPhase z (x, y + 2 * Real.pi) = fourierPhase z (x, y) + (z.2 : ℝ) * (2 * Real.pi) := by
    simp only [fourierPhase]
    ring
  dsimp only
  rw [hp, Real.cos_add_int_mul_two_pi]
  simp only [fourierCharacteristic, Real.cos_add_two_pi]

/-- The two rotated lattice coordinates separate exactly in the actual SRW transition probability. -/
theorem transitionProbability_product (n : ℕ) (z : Site) :
    transitionProbability n z = (4 * Real.pi ^ 2)⁻¹ *
      (cosineMoment n (z.1 + z.2) * cosineMoment n (z.1 - z.2)) := by
  rw [transitionProbability_fourier]
  have hrot := fourierBox_integral_rotation
    (fun θ ↦ fourierCharacteristic θ ^ n * Real.cos (fourierPhase z θ))
    (by unfold fourierCharacteristic fourierPhase; fun_prop)
    (fourierTransition_periodic_fst n z) (fourierTransition_periodic_snd n z)
  rw [← hrot]
  congr 1
  have hi (p : ℝ × ℝ) :
      fourierCharacteristic (p.1 + p.2, p.1 - p.2) ^ n * Real.cos (fourierPhase z (p.1 + p.2, p.1 - p.2)) =
      (Real.cos p.1 ^ n * Real.cos (((z.1 + z.2 : ℤ) : ℝ) * p.1)) *
        (Real.cos p.2 ^ n * Real.cos (((z.1 - z.2 : ℤ) : ℝ) * p.2)) -
      (Real.cos p.1 ^ n * Real.sin (((z.1 + z.2 : ℤ) : ℝ) * p.1)) *
        (Real.cos p.2 ^ n * Real.sin (((z.1 - z.2 : ℤ) : ℝ) * p.2)) := by
    rw [fourierCharacteristic_rotate, fourierPhase_rotate, mul_pow, Real.cos_add]
    ring
  simp_rw [hi]
  change (∫ p, _ ∂fourierIntervalMeasure.prod fourierIntervalMeasure) = _
  rw [integral_sub ((integrable_cosineMoment n (z.1 + z.2)).mul_prod (integrable_cosineMoment n (z.1 - z.2)))
    ((integrable_sineMoment n (z.1 + z.2)).mul_prod (integrable_sineMoment n (z.1 - z.2))),
    integral_prod_mul (fun t ↦ Real.cos t ^ n * Real.cos (((z.1 + z.2 : ℤ) : ℝ) * t))
      (fun t ↦ Real.cos t ^ n * Real.cos (((z.1 - z.2 : ℤ) : ℝ) * t)),
    integral_prod_mul (fun t ↦ Real.cos t ^ n * Real.sin (((z.1 + z.2 : ℤ) : ℝ) * t))
      (fun t ↦ Real.cos t ^ n * Real.sin (((z.1 - z.2 : ℤ) : ℝ) * t))]
  change cosineMoment _ _ * cosineMoment _ _ - sineMoment _ _ * sineMoment _ _ = _
  rw [sineMoment_eq_zero, zero_mul, sub_zero]

end SRWTightness
