import SRWTightness.SRWReturnProbability
import SRWTightness.FourierCharacteristicDecay

open MeasureTheory

namespace SRWTightness

theorem transitionProbability_le_return_even (m n : ℕ) (hmn : 2 * m ≤ n) (z : Site) :
    transitionProbability n z ≤ transitionProbability (2 * m) 0 := by
  rw [transitionProbability_fourier, transitionProbability_fourier]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono
  · exact continuous_integrable_fourierBox _ (by unfold fourierCharacteristic fourierPhase; fun_prop)
  · exact continuous_integrable_fourierBox _ (by unfold fourierCharacteristic fourierPhase; fun_prop)
  intro θ
  simp only [fourierPhase, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_mul, zero_add,
    Real.cos_zero, mul_one]
  calc
    _ ≤ |fourierCharacteristic θ ^ n * Real.cos ((z.1 : ℝ) * θ.1 + (z.2 : ℝ) * θ.2)| := le_abs_self _
    _ ≤ |fourierCharacteristic θ| ^ n := by
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    _ ≤ |fourierCharacteristic θ| ^ (2 * m) :=
      pow_le_pow_of_le_one (abs_nonneg _) (abs_fourierCharacteristic_le_one θ) hmn
    _ = fourierCharacteristic θ ^ (2 * m) := by
      rw [pow_mul, sq_abs, pow_mul]

end SRWTightness
