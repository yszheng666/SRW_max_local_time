import SRWTightness.SRWGaussianHeatKernelOdd

open MeasureTheory

namespace SRWTightness

theorem transitionProbability_nonneg (n : ℕ) (z : Site) : 0 ≤ transitionProbability n z := measureReal_nonneg

theorem transitionProbability_le_one (n : ℕ) (z : Site) : transitionProbability n z ≤ 1 := by
  unfold transitionProbability
  exact (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)).trans_eq (by simp)

theorem exp_neg_le_one_div (x : ℝ) (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  apply (le_div_iff₀ hx).2
  have h := Real.mul_exp_neg_le_exp_neg_one x
  have h1 : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  nlinarith

theorem transitionProbability_even_distance_le (n : ℕ) (hn : 0 < n) (z : Site) (hz : 0 < normSq z) :
    transitionProbability (2 * n) z ≤ 4 / (Real.pi * normSq z) := by
  refine (transitionProbability_even_gaussian_le n hn z).trans ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (1 / (Real.pi * n)) * (1 / (normSq z / (4 * n))) :=
      mul_le_mul_of_nonneg_left (exp_neg_le_one_div _ (by positivity)) (by positivity)
    _ = _ := by field_simp

theorem transitionProbability_odd_distance_le (n : ℕ) (hn : 0 < n) (z : Site) (hz : 0 < normSq z) :
    transitionProbability (2 * n + 1) z ≤ (8 * Real.exp 1) / (Real.pi * normSq z) := by
  refine (transitionProbability_odd_gaussian_le n hn z).trans ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (Real.exp 1 / (Real.pi * n)) * (1 / (normSq z / (8 * n))) :=
      mul_le_mul_of_nonneg_left (exp_neg_le_one_div _ (by positivity)) (by positivity)
    _ = _ := by field_simp

theorem transitionProbability_distance_le (n : ℕ) (hn : 2 ≤ n) (z : Site) (hz : 0 < normSq z) :
    transitionProbability n z ≤ (8 * Real.exp 1) / (Real.pi * normSq z) := by
  have hm : 0 < n / 2 := by omega
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn2 : n = 2 * (n / 2) := by omega
    rw [hn2]
    refine (transitionProbability_even_distance_le (n / 2) hm z hz).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  · have hn2 : n = 2 * (n / 2) + 1 := by omega
    simpa only [← hn2] using transitionProbability_odd_distance_le (n / 2) hm z hz

end SRWTightness
