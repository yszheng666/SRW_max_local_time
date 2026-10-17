import SRWTightness.SRWGaussianHeatKernel
import SRWTightness.SRWTransitionRecurrence
import SRWTightness.CoordinateBounds

namespace SRWTightness

theorem normSq_add_step_lower (z : Site) (d : Direction) :
    normSq z / 2 - 1 ≤ normSq (z + step d) := by
  have h := normSq_step d
  unfold normSq at h ⊢
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  nlinarith [sq_nonneg ((z.1 : ℝ) + 2 * (step d).1),
    sq_nonneg ((z.2 : ℝ) + 2 * (step d).2)]

theorem transitionProbability_odd_gaussian_le (n : ℕ) (hn : 0 < n) (z : Site) :
    transitionProbability (2 * n + 1) z ≤
      (Real.exp 1 / (Real.pi * n)) * Real.exp (-(normSq z / (8 * n))) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hd (d : Direction) : transitionProbability (2 * n) (z + step d) ≤
      (Real.exp 1 / (Real.pi * n)) * Real.exp (-(normSq z / (8 * n))) := by
    refine (transitionProbability_even_gaussian_le n hn (z + step d)).trans ?_
    have he : -(normSq (z + step d) / (4 * n)) ≤ 1 - normSq z / (8 * n) := by
      rw [← neg_div, div_le_iff₀ (by positivity : 0 < 4 * (n : ℝ))]
      have hi : (1 - normSq z / (8 * n)) * (4 * n) = 4 * n - normSq z / 2 := by
        field_simp
        <;> ring
      rw [hi]
      linarith [normSq_add_step_lower z d]
    calc
      _ ≤ (1 / (Real.pi * n)) * Real.exp (1 - normSq z / (8 * n)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring
  rw [transitionProbability_succ]
  calc
    _ ≤ (1 / 4 : ℝ) * ∑ _d : Direction,
        (Real.exp 1 / (Real.pi * n)) * Real.exp (-(normSq z / (8 * n))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ ↦ hd d)) (by norm_num)
    _ = _ := by simp [Direction]

end SRWTightness
