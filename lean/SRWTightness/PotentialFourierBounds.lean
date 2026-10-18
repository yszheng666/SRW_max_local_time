import SRWTightness.Path
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SRWTightness

noncomputable def fourierDenominator (θ : ℝ × ℝ) : ℝ :=
  1 - (Real.cos θ.1 + Real.cos θ.2) / 2

noncomputable def fourierPhase (z : Site) (θ : ℝ × ℝ) : ℝ :=
  (z.1 : ℝ) * θ.1 + (z.2 : ℝ) * θ.2

noncomputable def potentialFourierIntegrand (z : Site) (θ : ℝ × ℝ) : ℝ :=
  (1 - Real.cos (fourierPhase z θ)) / fourierDenominator θ

theorem fourierDenominator_nonneg (θ : ℝ × ℝ) : 0 ≤ fourierDenominator θ := by
  unfold fourierDenominator
  linarith [Real.cos_le_one θ.1, Real.cos_le_one θ.2]

theorem fourierDenominator_quadratic_lower (θ : ℝ × ℝ)
    (h1 : |θ.1| ≤ Real.pi) (h2 : |θ.2| ≤ Real.pi) :
    θ.1 ^ 2 + θ.2 ^ 2 ≤ Real.pi ^ 2 * fourierDenominator θ := by
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hc1 := Real.cos_le_one_sub_mul_cos_sq h1
  have hc2 := Real.cos_le_one_sub_mul_cos_sq h2
  rw [div_mul_eq_mul_div] at hc1 hc2
  have hb1 : (2 * θ.1 ^ 2) / Real.pi ^ 2 ≤ 1 - Real.cos θ.1 := by linarith
  have hb2 : (2 * θ.2 ^ 2) / Real.pi ^ 2 ≤ 1 - Real.cos θ.2 := by linarith
  have ha1 := (div_le_iff₀ hp).mp hb1
  have ha2 := (div_le_iff₀ hp).mp hb2
  unfold fourierDenominator
  nlinarith

theorem potentialFourierIntegrand_nonneg (z : Site) (θ : ℝ × ℝ) :
    0 ≤ potentialFourierIntegrand z θ :=
  div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (fourierDenominator_nonneg θ)

theorem potentialFourierIntegrand_bound (z : Site) (θ : ℝ × ℝ)
    (h1 : |θ.1| ≤ Real.pi) (h2 : |θ.2| ≤ Real.pi) :
    potentialFourierIntegrand z θ ≤ Real.pi ^ 2 * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) := by
  have hd := fourierDenominator_nonneg θ
  rcases eq_or_lt_of_le hd with hz | hp
  · simp only [potentialFourierIntegrand, ← hz, div_zero]
    positivity
  have hc := Real.one_sub_sq_div_two_le_cos (x := fourierPhase z θ)
  have hphase : (fourierPhase z θ) ^ 2 ≤
      ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) * (θ.1 ^ 2 + θ.2 ^ 2) := by
    unfold fourierPhase
    nlinarith [sq_nonneg ((z.1 : ℝ) * θ.2 - (z.2 : ℝ) * θ.1)]
  have hl := mul_le_mul_of_nonneg_left (fourierDenominator_quadratic_lower θ h1 h2)
    (add_nonneg (sq_nonneg (z.1 : ℝ)) (sq_nonneg (z.2 : ℝ)))
  unfold potentialFourierIntegrand
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (fourierPhase z θ)]

theorem measurable_potentialFourierIntegrand (z : Site) : Measurable (potentialFourierIntegrand z) := by
  unfold potentialFourierIntegrand fourierPhase fourierDenominator
  fun_prop

end SRWTightness
