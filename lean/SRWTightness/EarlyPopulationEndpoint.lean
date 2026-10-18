import SRWTightness.SourceGWOneRootMarginal

namespace SRWTightness

/-- The weighted population exponent is maximized at the barrier endpoint. -/
theorem early_population_exponent_endpoint (b d k e : ℝ)
    (hb : 0 < b) (hd : 0 < d) (hbd : b ≤ 4 * d) (hk : k ≤ b ^ 2 / 2) :
    2 * b + 4 * k / b - k / d + e ≤ 4 * b - b ^ 2 / (2 * d) + e := by
  have hc : 0 ≤ 4 / b - 1 / d := by
    have hh : 1 / d ≤ 4 / b := (div_le_div_iff₀ hd hb).mpr (by linarith)
    linarith
  have hh := mul_le_mul_of_nonneg_right hk hc
  calc
    _ = 2 * b + k * (4 / b - 1 / d) + e := by ring
    _ ≤ 2 * b + (b ^ 2 / 2) * (4 / b - 1 / d) + e := by linarith
    _ = _ := by field_simp; ring

/-- Multiplying a population tail by its conditional moment gives the endpoint bound. -/
theorem early_population_weight_endpoint (b d k e p : ℝ)
    (hb : 0 < b) (hd : 0 < d) (hbd : b ≤ 4 * d) (hk : k ≤ b ^ 2 / 2)
    (hp : p ≤ Real.exp (-k / d)) :
    p * Real.exp (2 * b + 4 * k / b + e) ≤
      Real.exp (4 * b - b ^ 2 / (2 * d) + e) := by
  calc
    _ ≤ Real.exp (-k / d) * Real.exp (2 * b + 4 * k / b + e) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (2 * b + 4 * k / b - k / d + e) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (early_population_exponent_endpoint b d k e hb hd hbd hk)

end SRWTightness
