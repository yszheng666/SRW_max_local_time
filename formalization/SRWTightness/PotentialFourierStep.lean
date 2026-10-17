import SRWTightness.PotentialFourierBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

namespace SRWTightness

theorem fourierPhase_add (x y : Site) (θ : ℝ × ℝ) :
    fourierPhase (x + y) θ = fourierPhase x θ + fourierPhase y θ := by
  simp only [fourierPhase, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

theorem sum_cos_fourierPhase_step (z : Site) (θ : ℝ × ℝ) :
    (∑ d : Direction, Real.cos (fourierPhase (z + step d) θ)) =
      2 * Real.cos (fourierPhase z θ) * (Real.cos θ.1 + Real.cos θ.2) := by
  simp only [fourierPhase_add]
  rw [Fin.sum_univ_four]
  rw [show step (0 : Direction) = (1, 0) from rfl,
    show step (1 : Direction) = (-1, 0) from rfl,
    show step (2 : Direction) = (0, 1) from rfl,
    show step (3 : Direction) = (0, -1) from rfl]
  norm_num [fourierPhase, Real.cos_add, Real.cos_neg, Real.sin_neg]
  ring

theorem potentialFourierIntegrand_poisson (z : Site) (θ : ℝ × ℝ)
    (hθ : fourierDenominator θ ≠ 0) :
    (1 / 4 : ℝ) * ∑ d : Direction, potentialFourierIntegrand (z + step d) θ -
      potentialFourierIntegrand z θ = Real.cos (fourierPhase z θ) := by
  simp only [potentialFourierIntegrand, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Direction, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [sum_cos_fourierPhase_step]
  field_simp [hθ]
  unfold fourierDenominator
  ring

end SRWTightness
