import SRWTightness.SourceRecordRadii
import Mathlib.Algebra.Order.Floor.Ring

namespace SRWTightness

/-- The manuscript's nonnegative root depth, used once the outer radius exceeds 32m. -/
noncomputable def sourceRootDepth (R m : ℝ) : ℕ := ⌊Real.log (R / (32 * m))⌋₊

/-- The floor choice gives the precise one-exponential-step bracket for the outer root scale. -/
theorem source_root_depth_bracket (R m : ℝ) (hm : 0 < m) (hR : 32 * m ≤ R) :
    32 * sourceRecordRadius m (sourceRootDepth R m) 0 ≤ R ∧
      R < 32 * Real.exp 1 * sourceRecordRadius m (sourceRootDepth R m) 0 := by
  have hR0 : 0 < R := by linarith
  have hq0 : 0 < R / (32 * m) := div_pos hR0 (by positivity)
  have hq1 : 1 ≤ R / (32 * m) := (one_le_div (by positivity)).mpr hR
  have hlog : 0 ≤ Real.log (R / (32 * m)) := Real.log_nonneg hq1
  have hu := Real.exp_le_exp.mpr (Nat.floor_le hlog)
  have hl := Real.exp_lt_exp.mpr (Nat.lt_floor_add_one (Real.log (R / (32 * m))))
  rw [Real.exp_log hq0] at hu hl
  rw [Real.exp_add] at hl
  have hq : R / (32 * m) * (32 * m) = R := div_mul_cancel₀ R (by positivity)
  have heu : 0 < Real.exp (⌊Real.log (R / (32 * m))⌋₊ : ℝ) := Real.exp_pos _
  simp only [sourceRecordRadius, Nat.cast_zero, sub_zero, sourceRootDepth]
  constructor <;> nlinarith

end SRWTightness
