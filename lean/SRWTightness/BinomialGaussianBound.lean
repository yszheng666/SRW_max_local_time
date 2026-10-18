import SRWTightness.BinomialRatio

namespace SRWTightness

theorem evenBinomialRatio_le_exp (n a : ℕ) (ha : a ≤ n) :
    evenBinomialRatio n a ≤ Real.exp (-((a : ℝ) ^ 2 / ((n : ℝ) + a))) := by
  by_cases ha0 : a = 0
  · subst a
    simp [evenBinomialRatio_zero]
  have ha' : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha0
  have hd : 0 < (n : ℝ) + a := by positivity
  have haux : ∀ i : ℕ, i ≤ a →
      evenBinomialRatio n i ≤ Real.exp (-((i : ℝ) ^ 2 / ((n : ℝ) + a))) := by
    intro i
    induction i with
    | zero => simp [evenBinomialRatio_zero]
    | succ i ih =>
      intro hi
      have hin : i ≤ n := by omega
      have hin' : (i : ℝ) ≤ n := by exact_mod_cast hin
      have hia' : (i : ℝ) + 1 ≤ a := by exact_mod_cast hi
      have hratio : ((n : ℝ) - i) / ((n : ℝ) + i + 1) ≤
          Real.exp (-(2 * (i : ℝ) + 1) / ((n : ℝ) + a)) := by
        have hfrac : (2 * (i : ℝ) + 1) / ((n : ℝ) + a) ≤
            (2 * (i : ℝ) + 1) / ((n : ℝ) + i + 1) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
        have heq : ((n : ℝ) - i) / ((n : ℝ) + i + 1) =
            1 - (2 * (i : ℝ) + 1) / ((n : ℝ) + i + 1) := by
          have hne : (n : ℝ) + i + 1 ≠ 0 := by positivity
          field_simp
          <;> ring
        rw [heq]
        have hex := Real.add_one_le_exp (-(2 * (i : ℝ) + 1) / ((n : ℝ) + a))
        simp only [neg_div] at hex ⊢
        linarith
      rw [evenBinomialRatio_succ n i hin, mul_div_assoc]
      calc
        _ ≤ Real.exp (-((i : ℝ) ^ 2 / ((n : ℝ) + a))) *
            Real.exp (-(2 * (i : ℝ) + 1) / ((n : ℝ) + a)) :=
          mul_le_mul (ih (by omega)) hratio (div_nonneg (sub_nonneg.mpr hin') (by positivity))
            (Real.exp_nonneg _)
        _ = _ := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
  exact haux a le_rfl

end SRWTightness
