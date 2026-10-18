import SRWTightness.SourceRootDepth

namespace SRWTightness

/-- The root return logarithm grows by one per source level, with an explicit uniform constant. -/
theorem source_root_log_denominator (R m H : ℝ) (ℓ k : ℕ) (hm : 0 < m)
    (hR : 0 < R) (hhalf : 2 * H ≤ sourceRecordRadius m ℓ (k + 1))
    (houter : R ≤ 32 * Real.exp 1 * sourceRecordRadius m ℓ 0) :
    Real.log (2 * R / (sourceRecordRadius m ℓ (k + 1) - H)) ≤
      (k : ℝ) + (Real.log 32 + 2 * Real.log 2 + 2) := by
  have hp : 0 < sourceRecordRadius m ℓ (k + 1) := by
    unfold sourceRecordRadius
    positivity
  have ha : 0 < sourceRecordRadius m ℓ (k + 1) - H := by linarith
  have hupper := Real.log_le_log hR houter
  have hlower := Real.log_le_log (by positivity : 0 < sourceRecordRadius m ℓ (k + 1) / 2)
    (show sourceRecordRadius m ℓ (k + 1) / 2 ≤ sourceRecordRadius m ℓ (k + 1) - H by linarith)
  have hroot : Real.log (sourceRecordRadius m ℓ 0) = Real.log m + (ℓ : ℝ) := by
    simp [sourceRecordRadius, Real.log_mul hm.ne' (Real.exp_pos _).ne']
  have hchild : Real.log (sourceRecordRadius m ℓ (k + 1)) =
      Real.log m + (ℓ : ℝ) - ((k : ℝ) + 1) := by
    simp [sourceRecordRadius, Real.log_mul hm.ne' (Real.exp_pos _).ne', Nat.cast_add,
      Nat.cast_one]
    ring
  have hrootpos : 0 < sourceRecordRadius m ℓ 0 := by unfold sourceRecordRadius; positivity
  rw [Real.log_mul (by positivity : (32 * Real.exp 1 : ℝ) ≠ 0) hrootpos.ne',
    Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) (Real.exp_pos 1).ne', Real.log_exp, hroot] at hupper
  rw [Real.log_div hp.ne' (by norm_num : (2 : ℝ) ≠ 0), hchild] at hlower
  rw [Real.log_div (by positivity : (2 * R) ≠ 0) ha.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hR.ne']
  linarith

end SRWTightness
