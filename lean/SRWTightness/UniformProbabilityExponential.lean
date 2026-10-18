import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SRWTightness

/-- Fixed positive probability comparisons are absorbed by any sufficiently large exponent. -/
theorem uniform_probability_exponential (p q c U E : ℝ) (hq : 0 ≤ q)
    (hc : 0 < c) (hU : 0 < U) (hlo : c * q ≤ p) (hhi : p ≤ U * q)
    (hEc : |Real.log c| ≤ E) (hEU : |Real.log U| ≤ E) :
    Real.exp (-E) * q ≤ p ∧ p ≤ Real.exp E * q := by
  have hcE : Real.exp (-E) ≤ c := by
    rw [← Real.exp_log hc]
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs (Real.log c)]
  have hUE : U ≤ Real.exp E := by
    rw [← Real.exp_log hU]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hEU)
  exact ⟨(mul_le_mul_of_nonneg_right hcE hq).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right hUE hq)⟩

end SRWTightness
