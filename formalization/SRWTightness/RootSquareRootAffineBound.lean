import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Equation 8.21: the positive-barrier affine majorant for the root square root. -/
theorem root_square_root_affine_bound (K b : ℝ) (hK : 0 ≤ K) (hb : 0 < b) :
    2 * Real.sqrt (2 * K) ≤ b + 2 * K / b := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * K by positivity)
  have hh : 2 * Real.sqrt (2 * K) ≤ (b ^ 2 + 2 * K) / b :=
    (le_div_iff₀ hb).2 (by nlinarith [sq_nonneg (b - Real.sqrt (2 * K))])
  convert hh using 1
  field_simp
  <;> ring

end SRWTightness
