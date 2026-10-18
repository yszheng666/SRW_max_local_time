import SRWTightness.SRWFourierInversion
import SRWTightness.PotentialFourierPartial
import SRWTightness.PotentialKernelPoisson

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

theorem integrable_fourier_transition_integrand (n : ℕ) (z : Site) :
    Integrable (fun θ ↦ fourierCharacteristic θ ^ n * Real.cos (fourierPhase z θ)) fourierBoxMeasure := by
  have hi := (integrable_joint_cos_position n z).integral_prod_right
  simpa only [integral_cos_position] using hi

theorem integrable_fourier_difference (n : ℕ) (z : Site) :
    Integrable (fun θ ↦ fourierCharacteristic θ ^ n * (1 - Real.cos (fourierPhase z θ)))
      fourierBoxMeasure := by
  have hc := integrable_fourier_transition_integrand n (0 : Site)
  simp only [fourierPhase, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_mul, zero_add,
    Real.cos_zero, mul_one] at hc
  apply (hc.sub (integrable_fourier_transition_integrand n z)).congr
  exact Filter.Eventually.of_forall (fun θ ↦ by dsimp only [Pi.sub_apply]; ring)

theorem transitionProbability_difference_fourier (n : ℕ) (z : Site) :
    transitionProbability n 0 - transitionProbability n z =
      (4 * Real.pi ^ 2)⁻¹ * ∫ θ, fourierCharacteristic θ ^ n * (1 - Real.cos (fourierPhase z θ))
        ∂fourierBoxMeasure := by
  rw [transitionProbability_fourier, transitionProbability_fourier, ← mul_sub,
    ← integral_sub (integrable_fourier_transition_integrand n 0) (integrable_fourier_transition_integrand n z)]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro θ
  simp only [fourierPhase, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_mul, zero_add,
    Real.cos_zero, mul_one]
  ring

theorem potentialKernel_partial_sum (z : Site) (N : ℕ) :
    (∑ n ∈ Finset.range N, (transitionProbability n 0 - transitionProbability n z)) =
      (4 * Real.pi ^ 2)⁻¹ * ∫ θ, potentialFourierPartial z N θ ∂fourierBoxMeasure := by
  simp_rw [transitionProbability_difference_fourier]
  rw [← Finset.mul_sum, ← integral_finsetSum (Finset.range N)
    (fun n _ ↦ integrable_fourier_difference n z)]
  congr 1
  apply integral_congr_ae
  filter_upwards [fourierDenominator_ae_ne_zero] with θ hθ
  exact (potentialFourierPartial_eq_sum z N θ hθ).symm

/-- The constructed Fourier potential kernel is the limit of actual SRW transition-probability differences. -/
theorem potentialKernel_eq_transition_limit (z : Site) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, (transitionProbability n 0 - transitionProbability n z))
      atTop (𝓝 (potentialKernel z)) := by
  simp_rw [potentialKernel_partial_sum]
  exact (potentialFourierPartial_integral_tendsto z).const_mul (4 * Real.pi ^ 2)⁻¹

end SRWTightness
