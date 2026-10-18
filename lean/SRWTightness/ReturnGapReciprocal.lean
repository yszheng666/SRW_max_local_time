import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SRWTightness

/-- A small numerator error can be absorbed by adding one to the logarithmic denominator bound. -/
theorem return_gap_reciprocal (K a d v : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hv : 0 ≤ v) (hden : d ≤ v) (hsmall : K * (v + 1) ≤ a) :
    1 / (v + 1) ≤ (1 - K / a) / d := by
  have hv1 : 0 < v + 1 := by linarith
  have he : K / a ≤ 1 / (v + 1) := (div_le_div_iff₀ ha hv1).mpr (by simpa using hsmall)
  apply (le_div_iff₀ hd).mpr
  calc
    1 / (v + 1) * d ≤ 1 / (v + 1) * v :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = 1 - 1 / (v + 1) := by field_simp; ring
    _ ≤ 1 - K / a := by linarith

end SRWTightness
