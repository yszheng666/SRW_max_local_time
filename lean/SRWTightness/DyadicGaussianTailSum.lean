import SRWTightness.DyadicChainingWeights

namespace SRWTightness

/-- The summed scale tails retain a Gaussian factor in the common threshold. -/
theorem dyadic_gaussian_tail_sum_bound (u : ℝ) (hu : 0 ≤ u) :
    Summable (fun n : ℕ ↦ 162 * (16 : ℝ) ^ n * Real.exp (-((u + n + 1) ^ 2) / 2)) ∧
    (∑' n : ℕ, 162 * (16 : ℝ) ^ n * Real.exp (-((u + n + 1) ^ 2) / 2)) ≤
      (162 * ∑' n : ℕ, (16 : ℝ) ^ n * Real.exp (-((n : ℝ) + 1) ^ 2 / 2)) *
        Real.exp (-u ^ 2 / 2) := by
  let b := fun n : ℕ ↦ (162 * Real.exp (-u ^ 2 / 2)) *
    ((16 : ℝ) ^ n * Real.exp (-((n : ℝ) + 1) ^ 2 / 2))
  have hb : Summable b := dyadic_gaussian_edge_weight_summable.mul_left _
  have hle (n : ℕ) : 162 * (16 : ℝ) ^ n * Real.exp (-((u + n + 1) ^ 2) / 2) ≤ b n := by
    have he : Real.exp (-((u + n + 1) ^ 2) / 2) ≤
        Real.exp (-u ^ 2 / 2) * Real.exp (-((n : ℝ) + 1) ^ 2 / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hu (show 0 ≤ (n : ℝ) + 1 by positivity)]
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 162 * (16 : ℝ) ^ n by positivity)
    dsimp [b]
    nlinarith
  have hs := hb.of_nonneg_of_le (fun n ↦ by positivity) hle
  refine ⟨hs, (hs.tsum_le_tsum hle hb).trans_eq ?_⟩
  rw [show b = fun n : ℕ ↦ (162 * Real.exp (-u ^ 2 / 2)) *
    ((16 : ℝ) ^ n * Real.exp (-((n : ℝ) + 1) ^ 2 / 2)) from rfl, tsum_mul_left]
  ring

end SRWTightness
