import SRWTightness.SRWFourierProduct
import SRWTightness.PotentialFourierStep

open MeasureTheory

namespace SRWTightness

theorem transitionProbability_succ (n : ℕ) (z : Site) :
    transitionProbability (n + 1) z = (1 / 4 : ℝ) * ∑ d : Direction, transitionProbability n (z + step d) := by
  simp_rw [transitionProbability_fourier]
  rw [← Finset.mul_sum]
  have he (θ : ℝ × ℝ) : fourierCharacteristic θ ^ (n + 1) * Real.cos (fourierPhase z θ) =
      (1 / 4 : ℝ) * ∑ d : Direction, fourierCharacteristic θ ^ n * Real.cos (fourierPhase (z + step d) θ) := by
    rw [← Finset.mul_sum, sum_cos_fourierPhase_step, pow_succ]
    unfold fourierCharacteristic
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum Finset.univ]
  · ring
  · intro d hd
    exact continuous_integrable_fourierBox _ (by unfold fourierCharacteristic fourierPhase; fun_prop)

end SRWTightness
