import SRWTightness.PotentialKernelGreen
import Mathlib.Tactic.FinCases

open MeasureTheory

namespace SRWTightness

theorem potentialFourierIntegrand_swap (z : Site) (θ : ℝ × ℝ) :
    potentialFourierIntegrand z.swap θ = potentialFourierIntegrand z θ.swap := by
  have hp : fourierPhase z.swap θ = fourierPhase z θ.swap := by
    simp only [fourierPhase, Prod.swap]
    ring
  have hd : fourierDenominator θ = fourierDenominator θ.swap := by
    simp only [fourierDenominator, Prod.swap]
    ring
  unfold potentialFourierIntegrand
  rw [hp, hd]

theorem potentialKernel_swap (z : Site) : potentialKernel z.swap = potentialKernel z := by
  unfold potentialKernel
  congr 1
  calc
    _ = ∫ θ, potentialFourierIntegrand z θ.swap ∂fourierBoxMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (potentialFourierIntegrand_swap z)
    _ = _ := integral_prod_swap (potentialFourierIntegrand z)

theorem potentialKernel_step_eq (d : Direction) : potentialKernel (step d) = potentialKernel (1, 0) := by
  fin_cases d
  · rfl
  · exact potentialKernel_neg (1, 0)
  · exact potentialKernel_swap (1, 0)
  · exact (potentialKernel_neg (0, 1)).trans (potentialKernel_swap (1, 0))

/-- The canonical normalization of the SRW potential kernel at each nearest neighbor. -/
theorem potentialKernel_step (d : Direction) : potentialKernel (step d) = 1 := by
  have hp := potentialKernel_poisson (0 : Site)
  simp only [zero_add, potentialKernel_zero, sub_zero, ite_true] at hp
  simp_rw [potentialKernel_step_eq] at hp
  simp only [Finset.sum_const, Finset.card_univ, Direction, Fintype.card_fin, nsmul_eq_mul] at hp
  rw [potentialKernel_step_eq]
  linarith

end SRWTightness
