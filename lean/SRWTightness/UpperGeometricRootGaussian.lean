import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace SRWTightness

/-- A geometric return weight is bounded uniformly by the source exponential weight. -/
theorem upper_geometric_root_exponential (q : ℝ) (J : ℕ) (hq : 1 ≤ q) (hJ : 0 < J) :
    (1 - 1 / q) ^ (J - 1) ≤ Real.exp 1 * Real.exp (-(J : ℝ) / q) := by
  have hq0 : 0 < q := by linarith
  have hinv : 1 / q ≤ 1 := (div_le_one hq0).mpr hq
  have hρ : 0 ≤ 1 - 1 / q := by linarith
  have hρexp : 1 - 1 / q ≤ Real.exp (-1 / q) := by
    convert Real.add_one_le_exp (-1 / q) using 1 <;> ring
  have hp := pow_le_pow_left₀ hρ hρexp (J - 1)
  rw [← Real.exp_nat_mul] at hp
  have hcast : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have he : ((J - 1 : ℕ) : ℝ) * (-1 / q) ≤ 1 + -(J : ℝ) / q := by
    rw [hcast]
    have hid : ((J : ℝ) - 1) * (-1 / q) = -(J : ℝ) / q + 1 / q := by ring
    rw [hid]
    linarith
  exact hp.trans (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr he)

/-- The root exponent completes its square without altering the extracted source coefficient. -/
theorem upper_geometric_root_square (q a x : ℝ) (hq : 0 < q) (hx : 0 ≤ x) :
    -x / q + a * Real.sqrt (2 * x) =
      a ^ 2 * q / 2 - (Real.sqrt (2 * x) - a * q) ^ 2 / (2 * q) := by
  have hs : (Real.sqrt (2 * x)) ^ 2 = 2 * x := Real.sq_sqrt (by positivity)
  rw [mul_comm (2 : ℝ) x] at hs
  field_simp [hq.ne']
  nlinarith

/-- Root weights factor into the exact leading exponential and a centered Gaussian kernel. -/
theorem upper_geometric_root_gaussian (q a : ℝ) (J : ℕ) (hq : 1 ≤ q) (hJ : 0 < J) :
    (1 - 1 / q) ^ (J - 1) * (J : ℝ) ^ (1 / 4 : ℝ) *
        Real.exp (a * Real.sqrt (2 * (J : ℝ))) ≤
      Real.exp 1 * Real.exp (a ^ 2 * q / 2) *
        ((J : ℝ) ^ (1 / 4 : ℝ) *
          Real.exp (-((Real.sqrt (2 * (J : ℝ)) - a * q) ^ 2 / (2 * q)))) := by
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (upper_geometric_root_exponential q J hq hJ)
      (Real.rpow_nonneg (Nat.cast_nonneg J) (1 / 4 : ℝ)))
    (Real.exp_nonneg (a * Real.sqrt (2 * (J : ℝ))))
  apply hb.trans_eq
  have he := upper_geometric_root_square q a (J : ℝ) (by linarith) (Nat.cast_nonneg _)
  rw [show Real.exp 1 * Real.exp (-(J : ℝ) / q) * (J : ℝ) ^ (1 / 4 : ℝ) *
      Real.exp (a * Real.sqrt (2 * (J : ℝ))) =
        Real.exp 1 * (J : ℝ) ^ (1 / 4 : ℝ) *
          Real.exp (-(J : ℝ) / q + a * Real.sqrt (2 * (J : ℝ))) by
    rw [Real.exp_add]; ring]
  rw [he, sub_eq_add_neg, Real.exp_add]
  ring

end SRWTightness
