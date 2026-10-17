import SRWTightness.PotentialFourierStep
import SRWTightness.FourierBoxOrthogonality

open MeasureTheory

namespace SRWTightness

theorem fourierDenominator_ae_ne_zero :
    ∀ᵐ θ ∂fourierBoxMeasure, fourierDenominator θ ≠ 0 := by
  have hn : ∀ᵐ t ∂fourierIntervalMeasure, t ≠ 0 :=
    ae_restrict_of_ae (by rw [ae_iff]; simp)
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := fourierIntervalMeasure)
    (ν := fourierIntervalMeasure)).ae hn
  filter_upwards [fourierBoxMeasure_support, h1] with θ hθ hnθ
  have hb := fourierDenominator_quadratic_lower θ hθ.1 hθ.2
  intro hz
  rw [hz, mul_zero] at hb
  have hp := sq_pos_of_ne_zero hnθ
  nlinarith [sq_nonneg θ.2]

/-- The explicit Fourier potential kernel has the exact SRW Poisson equation. -/
theorem potentialKernel_poisson (z : Site) :
    (1 / 4 : ℝ) * ∑ d : Direction, potentialKernel (z + step d) - potentialKernel z =
      if z = 0 then 1 else 0 := by
  have hi : (∫ θ, (1 / 4 : ℝ) * ∑ d : Direction, potentialFourierIntegrand (z + step d) θ -
      potentialFourierIntegrand z θ ∂fourierBoxMeasure) =
      ∫ θ, Real.cos (fourierPhase z θ) ∂fourierBoxMeasure := by
    apply integral_congr_ae
    filter_upwards [fourierDenominator_ae_ne_zero] with θ hθ
    exact potentialFourierIntegrand_poisson z θ hθ
  rw [integral_sub ((integrable_finsetSum Finset.univ
      (fun d _ ↦ integrable_potentialFourierIntegrand (z + step d))).const_mul _)
      (integrable_potentialFourierIntegrand z), integral_const_mul,
    integral_finsetSum Finset.univ (fun d _ ↦ integrable_potentialFourierIntegrand (z + step d)),
    fourierBox_integral_cos_phase] at hi
  unfold potentialKernel
  rw [← Finset.mul_sum]
  have he := congrArg (fun t : ℝ ↦ (4 * Real.pi ^ 2)⁻¹ * t) hi
  by_cases hz : z = 0
  · simp only [if_pos hz] at he ⊢
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at he ⊢
    nlinarith
  · simp only [if_neg hz, mul_zero] at he ⊢
    nlinarith

end SRWTightness
