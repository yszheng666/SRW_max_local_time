import SRWTightness.BesselThreeKernel
import SRWTightness.BridgeExponentialBounds
import Mathlib.Tactic.Positivity

namespace SRWTightness

/-- Separate the Gaussian and reflection factors in the explicit BES(3) kernel. -/
theorem besselThreeDensity_factor (s x y : ℝ) :
    besselThreeDensity s x y =
      (y / x) * (Real.exp (-((x - y) ^ 2) / (2 * s)) *
        (1 - Real.exp (-(2 * x * y / s)))) / Real.sqrt (2 * Real.pi * s) := by
  have he : -((x + y) ^ 2) / (2 * s) =
      -((x - y) ^ 2) / (2 * s) + -(2 * x * y / s) := by ring
  unfold besselThreeDensity killedBrownianDensity
  rw [he, Real.exp_add]
  ring

/-- The uniform kernel upper bound used for the numerator of the bridge density. -/
theorem besselThreeDensity_upper (s x y : ℝ) (hs : 0 < s)
    (hx : 0 < x) (hy : 0 < y) :
    besselThreeDensity s x y ≤ 2 * y ^ 2 / (s * Real.sqrt (2 * Real.pi * s)) := by
  have hz : 0 ≤ 2 * x * y / s := by positivity
  have ha : Real.exp (-((x - y) ^ 2) / (2 * s)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (by positivity))
  have hb : 1 - Real.exp (-(2 * x * y / s)) ≤ 2 * x * y / s := by
    linarith [Real.add_one_le_exp (-(2 * x * y / s))]
  have hprod : Real.exp (-((x - y) ^ 2) / (2 * s)) *
      (1 - Real.exp (-(2 * x * y / s))) ≤ 2 * x * y / s := by
    calc
      _ ≤ Real.exp (-((x - y) ^ 2) / (2 * s)) * (2 * x * y / s) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ ≤ 1 * (2 * x * y / s) := mul_le_mul_of_nonneg_right ha hz
      _ = _ := one_mul _
  calc
    _ = _ := besselThreeDensity_factor s x y
    _ ≤ (y / x) * (2 * x * y / s) / Real.sqrt (2 * Real.pi * s) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (div_nonneg hy.le hx.le))
        (Real.sqrt_nonneg _)
    _ = _ := by field_simp

/-- A lower kernel bound when the endpoint product and Gaussian exponent are controlled. -/
theorem besselThreeDensity_lower (s x y M : ℝ) (hs : 0 < s)
    (hx : 0 < x) (hy : 0 < y) (hxy : 2 * x * y / s ≤ 1)
    (hM : (x - y) ^ 2 / (2 * s) ≤ M) :
    Real.exp (-M) * y ^ 2 / (s * Real.sqrt (2 * Real.pi * s)) ≤
      besselThreeDensity s x y := by
  have hz : 0 ≤ 2 * x * y / s := by positivity
  have he : Real.exp (-M) ≤ Real.exp (-((x - y) ^ 2) / (2 * s)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    exact neg_le_neg hM
  have hp := mul_le_mul he (bridge_reflection_factor_bounds _ hz hxy).1
    (by positivity : 0 ≤ (2 * x * y / s) / 2) (Real.exp_pos _).le
  calc
    _ = (y / x) * (Real.exp (-M) * ((2 * x * y / s) / 2)) /
        Real.sqrt (2 * Real.pi * s) := by field_simp
    _ ≤ (y / x) * (Real.exp (-((x - y) ^ 2) / (2 * s)) *
        (1 - Real.exp (-(2 * x * y / s)))) / Real.sqrt (2 * Real.pi * s) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (div_nonneg hy.le hx.le))
        (Real.sqrt_nonneg _)
    _ = _ := (besselThreeDensity_factor s x y).symm

end SRWTightness
