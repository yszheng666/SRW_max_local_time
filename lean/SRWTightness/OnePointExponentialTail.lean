import SRWTightness.TailGeometric
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory

namespace SRWTightness

theorem occupation_tail_exp_upper (D : Finset Site) (x y : Site) (hy : y ∈ D)
    (k : ℕ) (hk : 1 ≤ k) (H : ℝ) (hH : killedGreen D y y ≤ H) :
    pathLaw.real {ω | k ≤ domainLocalTime D x y ω} ≤
      (killedGreen D x y / killedGreen D y y) * Real.exp (-((k - 1 : ℕ) : ℝ) / H) := by
  have hG1 := killedGreen_diag_ge_one D y hy
  have hG : 0 < killedGreen D y y := by linarith
  have hHp : 0 < H := hG.trans_le hH
  rw [occupation_probability_ge D x y hy k hk]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (killedGreen_nonneg D x y) hG.le)
  have hq : 0 ≤ 1 - 1 / killedGreen D y y := by
    have hh := (div_le_one hG).mpr hG1
    linarith
  have hp := pow_le_pow_left₀ hq (Real.one_sub_le_exp_neg (1 / killedGreen D y y)) (k - 1)
  rw [← Real.exp_nat_mul] at hp
  refine hp.trans (Real.exp_le_exp.mpr ?_)
  have hi : (1 : ℝ) / H ≤ 1 / killedGreen D y y :=
    one_div_le_one_div_of_le hG hH
  have hm := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (k - 1))
  simpa only [mul_neg, mul_one_div, neg_div] using neg_le_neg hm

theorem occupation_tail_exp_prefactor_upper (D : Finset Site) (x y : Site) (hy : y ∈ D)
    (k : ℕ) (hk : 1 ≤ k) (d H F : ℝ) (hd : 0 < d)
    (hlo : d ≤ killedGreen D y y) (hhi : killedGreen D y y ≤ H)
    (hf : killedGreen D x y ≤ F) :
    pathLaw.real {ω | k ≤ domainLocalTime D x y ω} ≤
      (F / d) * Real.exp (-((k - 1 : ℕ) : ℝ) / H) := by
  refine (occupation_tail_exp_upper D x y hy k hk H hhi).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (div_le_div_of_nonneg_left (killedGreen_nonneg D x y) hd hlo).trans
    (div_le_div_of_nonneg_right hf hd.le)

end SRWTightness
