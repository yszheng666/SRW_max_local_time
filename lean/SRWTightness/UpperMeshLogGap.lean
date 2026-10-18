import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- The inward mesh buffer loses only three times its relative size in the logarithmic gap. -/
theorem upper_mesh_log_gap (r H δ : ℝ) (hr : 0 < r) (hH : 0 ≤ H)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (hsmall : H ≤ δ * r) :
    1 - 3 * δ ≤ Real.log ((Real.exp 1 * r - H) / (r + H)) := by
  have hminus : 0 < 1 - δ := by linarith
  have hplus : 0 < 1 + δ := by linarith
  have hb : 0 < r + H := by linarith
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hc : Real.exp 1 * r * (1 - δ) ≤ Real.exp 1 * r - H := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (mul_nonneg hδ hr.le)]
  have hratio : Real.exp 1 * (1 - δ) / (1 + δ) ≤
      (Real.exp 1 * r - H) / (r + H) := by
    calc
      _ = (Real.exp 1 * r * (1 - δ)) / (r * (1 + δ)) := by field_simp
      _ ≤ (Real.exp 1 * r * (1 - δ)) / (r + H) :=
        div_le_div_of_nonneg_left (by positivity) hb (by nlinarith)
      _ ≤ _ := div_le_div_of_nonneg_right hc hb.le
  have hinv : 1 / (1 - δ) ≤ 1 + 2 * δ :=
    (div_le_iff₀ hminus).mpr (by nlinarith)
  have hlo := Real.one_sub_inv_le_log_of_pos hminus
  rw [inv_eq_one_div] at hlo
  have hhi := Real.log_le_sub_one_of_pos hplus
  calc
    _ ≤ 1 + Real.log (1 - δ) - Real.log (1 + δ) := by linarith
    _ = Real.log (Real.exp 1 * (1 - δ) / (1 + δ)) := by
      rw [Real.log_div (mul_pos (Real.exp_pos _) hminus).ne' hplus.ne',
        Real.log_mul (Real.exp_ne_zero _) hminus.ne', Real.log_exp]
    _ ≤ _ := Real.log_le_log (by positivity) hratio

/-- A reciprocal-level numerator error is absorbed into one fixed denominator shift. -/
theorem upper_mesh_shifted_return_gap (j C d q : ℝ) (hj : 0 ≤ j) (hC : 1 ≤ C)
    (hd : 0 < d) (hden : d ≤ j + C) (hnum : 1 - 1 / (4 * (j + 1)) ≤ q) :
    1 / (j + (2 * C + 2)) ≤ q / d := by
  have hJ : 0 < 4 * (j + 1) := by positivity
  have hshift : 0 < j + (2 * C + 2) := by linarith
  have hfrac : 1 / (4 * (j + 1)) ≤ (C + 2) / (j + (2 * C + 2)) := by
    apply (div_le_div_iff₀ hJ hshift).mpr
    nlinarith [mul_nonneg hj (show 0 ≤ C by linarith)]
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ (1 / (j + (2 * C + 2))) * (j + C) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = 1 - (C + 2) / (j + (2 * C + 2)) := by field_simp; ring
    _ ≤ 1 - 1 / (4 * (j + 1)) := by linarith
    _ ≤ q := hnum

end SRWTightness
