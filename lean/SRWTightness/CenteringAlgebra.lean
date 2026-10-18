import SRWTightness.Targets
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

theorem diskCenter_quotient_difference (R Q : ℝ) (hQ : 1 ≤ Q) (hR : Q < R) :
    diskCenter R - diskCenter (R / Q) = (2 / Real.sqrt Real.pi) * Real.log Q +
      (1 / Real.sqrt Real.pi) * Real.log (1 - Real.log Q / Real.log R) := by
  have hQ0 : 0 < Q := by linarith
  have hR0 : 0 < R := by linarith
  have hlR : 0 < Real.log R := Real.log_pos (by linarith)
  have hd : 0 < Real.log R - Real.log Q := sub_pos.mpr (Real.log_lt_log hQ0 hR)
  have he : 1 - Real.log Q / Real.log R = (Real.log R - Real.log Q) / Real.log R := by
    field_simp
  have hf : 0 < 1 - Real.log Q / Real.log R := by rw [he]; exact div_pos hd hlR
  have hp : Real.log R - Real.log Q = Real.log R * (1 - Real.log Q / Real.log R) := by
    field_simp
  have hlog : Real.log (Real.log (R / Q)) = Real.log (Real.log R) +
      Real.log (1 - Real.log Q / Real.log R) := by
    rw [Real.log_div hR0.ne' hQ0.ne', hp, Real.log_mul hlR.ne' hf.ne']
  unfold diskCenter
  rw [hlog, Real.log_div hR0.ne' hQ0.ne']
  ring

theorem diskCenter_quotient_difference_le (R Q : ℝ) (hQ : 1 ≤ Q) (hR : Q < R) :
    diskCenter R - diskCenter (R / Q) ≤ (2 / Real.sqrt Real.pi) * Real.log Q := by
  rw [diskCenter_quotient_difference R Q hQ hR]
  have hlR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hf : 0 < 1 - Real.log Q / Real.log R := by
    apply sub_pos.mpr
    apply (div_lt_one hlR).mpr
    exact Real.log_lt_log (by linarith) hR
  have hle : 1 - Real.log Q / Real.log R ≤ 1 := by linarith [div_nonneg hlQ hlR.le]
  have hlog : Real.log (1 - Real.log Q / Real.log R) ≤ 0 := Real.log_nonpos hf.le hle
  have hmul := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 1 / Real.sqrt Real.pi) hlog
  linarith

end SRWTightness
