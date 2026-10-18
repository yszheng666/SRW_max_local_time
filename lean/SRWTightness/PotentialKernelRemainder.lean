import SRWTightness.PotentialKernelSeries
import SRWTightness.SRWReturnBounds

open MeasureTheory Filter

namespace SRWTightness

theorem integrable_potentialFourier_remainder (z : Site) (N : ℕ) :
    Integrable (fun θ ↦ potentialFourierIntegrand z θ * fourierCharacteristic θ ^ N) fourierBoxMeasure := by
  apply ((integrable_potentialFourierIntegrand z).sub (integrable_potentialFourierPartial z N)).congr
  exact Eventually.of_forall (fun θ ↦ by dsimp only [Pi.sub_apply, potentialFourierPartial]; ring)

theorem potentialKernel_remainder_fourier (z : Site) (N : ℕ) :
    potentialKernel z - ∑ n ∈ Finset.range N, (transitionProbability n 0 - transitionProbability n z) =
      (4 * Real.pi ^ 2)⁻¹ * ∫ θ, potentialFourierIntegrand z θ * fourierCharacteristic θ ^ N
        ∂fourierBoxMeasure := by
  rw [potentialKernel_partial_sum]
  unfold potentialKernel
  rw [← mul_sub, ← integral_sub (integrable_potentialFourierIntegrand z) (integrable_potentialFourierPartial z N)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun θ ↦ by dsimp only [potentialFourierPartial]; ring)

/-- Even truncations have a nonnegative remainder controlled by the actual return probability. -/
theorem potentialKernel_even_remainder_bounds (z : Site) (N : ℕ) :
    0 ≤ potentialKernel z - ∑ n ∈ Finset.range (2 * N), (transitionProbability n 0 - transitionProbability n z) ∧
    potentialKernel z - ∑ n ∈ Finset.range (2 * N), (transitionProbability n 0 - transitionProbability n z) ≤
      Real.pi ^ 2 * normSq z * transitionProbability (2 * N) 0 := by
  rw [potentialKernel_remainder_fourier]
  have hp (θ : ℝ × ℝ) : 0 ≤ fourierCharacteristic θ ^ (2 * N) := by
    rw [pow_mul]
    positivity
  constructor
  · apply mul_nonneg (by positivity)
    exact integral_nonneg (fun θ ↦ mul_nonneg (potentialFourierIntegrand_nonneg z θ) (hp θ))
  · have hc : Integrable (fun θ ↦ fourierCharacteristic θ ^ (2 * N)) fourierBoxMeasure :=
      continuous_integrable_fourierBox _ (by unfold fourierCharacteristic; fun_prop)
    have hi : (∫ θ, potentialFourierIntegrand z θ * fourierCharacteristic θ ^ (2 * N) ∂fourierBoxMeasure) ≤
        (Real.pi ^ 2 * normSq z) * ∫ θ, fourierCharacteristic θ ^ (2 * N) ∂fourierBoxMeasure := by
      rw [← integral_const_mul]
      apply integral_mono_ae (integrable_potentialFourier_remainder z (2 * N)) (hc.const_mul _)
      filter_upwards [fourierBoxMeasure_support] with θ hθ
      exact mul_le_mul_of_nonneg_right (potentialFourierIntegrand_bound z θ hθ.1 hθ.2) (hp θ)
    have h := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (4 * Real.pi ^ 2)⁻¹)
    rw [transitionProbability_fourier]
    simp only [fourierPhase, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_mul, zero_add,
      Real.cos_zero, mul_one]
    nlinarith [h]

theorem potentialKernel_even_remainder_le (z : Site) (N : ℕ) (hN : 0 < N) :
    potentialKernel z - ∑ n ∈ Finset.range (2 * N), (transitionProbability n 0 - transitionProbability n z) ≤
      Real.pi * normSq z / N := by
  refine (potentialKernel_even_remainder_bounds z N).2.trans ?_
  calc
    _ ≤ Real.pi ^ 2 * normSq z * (1 / (Real.pi * N)) :=
      mul_le_mul_of_nonneg_left (transitionProbability_return_le N hN) (by unfold normSq; positivity)
    _ = _ := by field_simp

end SRWTightness
