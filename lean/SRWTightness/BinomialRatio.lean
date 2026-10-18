import SRWTightness.CentralBinomialBounds

namespace SRWTightness

noncomputable def evenBinomialRatio (n j : ℕ) : ℝ :=
  ((2 * n).choose (n + j) : ℝ) / (Nat.centralBinom n : ℝ)

theorem evenBinomialRatio_nonneg (n j : ℕ) : 0 ≤ evenBinomialRatio n j := by
  unfold evenBinomialRatio
  positivity

theorem evenBinomialRatio_zero (n : ℕ) : evenBinomialRatio n 0 = 1 := by
  unfold evenBinomialRatio
  simp only [add_zero, ← Nat.centralBinom_eq_two_mul_choose]
  exact div_self (by exact_mod_cast Nat.centralBinom_ne_zero n)

theorem evenBinomialRatio_succ (n j : ℕ) (hj : j ≤ n) :
    evenBinomialRatio n (j + 1) = evenBinomialRatio n j *
      ((n : ℝ) - j) / ((n : ℝ) + j + 1) := by
  have hh := Nat.choose_succ_right_eq (2 * n) (n + j)
  rw [show 2 * n - (n + j) = n - j by omega] at hh
  have hb := congrArg (fun k : ℕ ↦ (k : ℝ)) hh
  push_cast [Nat.cast_sub hj] at hb
  unfold evenBinomialRatio
  have hc : (Nat.centralBinom n : ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero n
  have hd : (n : ℝ) + j + 1 ≠ 0 := by positivity
  rw [show n + (j + 1) = n + j + 1 by omega]
  field_simp
  nlinarith [hb]

end SRWTightness
