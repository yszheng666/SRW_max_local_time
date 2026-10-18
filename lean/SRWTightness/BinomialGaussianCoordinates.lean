import SRWTightness.BinomialGaussianBound

namespace SRWTightness

theorem evenBinomialRatio_le_gaussian (n a : ℕ) (ha : a ≤ n) (hn : 0 < n) :
    evenBinomialRatio n a ≤ Real.exp (-((a : ℝ) ^ 2 / (2 * n))) := by
  refine (evenBinomialRatio_le_exp n a ha).trans ?_
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha' : (a : ℝ) ≤ n := by exact_mod_cast ha
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)

theorem binomial_coefficient_le_gaussian (n j : ℕ) (hj : j ≤ 2 * n) (hn : 0 < n) :
    ((2 * n).choose j : ℝ) / (Nat.centralBinom n : ℝ) ≤
      Real.exp (-(((j : ℝ) - n) ^ 2 / (2 * n))) := by
  by_cases hjn : j ≤ n
  · have h := evenBinomialRatio_le_gaussian n (n - j) (Nat.sub_le _ _) hn
    have hc : (2 * n).choose (n + (n - j)) = (2 * n).choose j := by
      rw [show n + (n - j) = 2 * n - j by omega]
      exact Nat.choose_symm hj
    unfold evenBinomialRatio at h
    rw [hc] at h
    have he : ((n - j : ℕ) : ℝ) ^ 2 = ((j : ℝ) - n) ^ 2 := by
      rw [Nat.cast_sub hjn]
      ring
    simpa only [he] using h
  · have hnj : n ≤ j := by omega
    have h := evenBinomialRatio_le_gaussian n (j - n) (by omega) hn
    unfold evenBinomialRatio at h
    rw [Nat.add_sub_of_le hnj, Nat.cast_sub hnj] at h
    exact h

end SRWTightness
