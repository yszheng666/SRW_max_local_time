import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- The positive-half-line killed Brownian transition density in source (7.15). -/
noncomputable def killedBrownianDensity (s x y : ℝ) : ℝ :=
  (Real.exp (-((x - y) ^ 2) / (2 * s)) -
    Real.exp (-((x + y) ^ 2) / (2 * s))) / Real.sqrt (2 * Real.pi * s)

/-- The BES(3) transition density in source (7.15), for positive arguments. -/
noncomputable def besselThreeDensity (s x y : ℝ) : ℝ :=
  (y / x) * killedBrownianDensity s x y

theorem killedBrownianDensity_symm (s x y : ℝ) :
    killedBrownianDensity s x y = killedBrownianDensity s y x := by
  have h : (x - y) ^ 2 = (y - x) ^ 2 := by ring
  simp only [killedBrownianDensity, h, add_comm x y]

theorem killedBrownianDensity_pos (s x y : ℝ) (hs : 0 < s)
    (hx : 0 < x) (hy : 0 < y) : 0 < killedBrownianDensity s x y := by
  apply div_pos
  · apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    apply (div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * s)).mpr
    nlinarith [mul_pos hx hy]
  · exact Real.sqrt_pos.mpr (by positivity)

theorem besselThreeDensity_pos (s x y : ℝ) (hs : 0 < s)
    (hx : 0 < x) (hy : 0 < y) : 0 < besselThreeDensity s x y :=
  mul_pos (div_pos hy hx) (killedBrownianDensity_pos s x y hs hx hy)

/-- The reversible weight is x squared, as used for the second half of the bridge. -/
theorem besselThreeDensity_reversible (s x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ 2 * besselThreeDensity s x y = y ^ 2 * besselThreeDensity s y x := by
  unfold besselThreeDensity
  rw [killedBrownianDensity_symm s y x]
  field_simp
  <;> ring

/-- Doob factors cancel in the bridge density at an intermediate positive location. -/
theorem besselThreeDensity_bridge_ratio (s t x y z : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    besselThreeDensity s x y * besselThreeDensity t y z /
        besselThreeDensity (s + t) x z =
      killedBrownianDensity s x y * killedBrownianDensity t y z /
        killedBrownianDensity (s + t) x z := by
  unfold besselThreeDensity
  by_cases h : killedBrownianDensity (s + t) x z = 0
  · simp [h]
  · field_simp
    <;> ring

end SRWTightness
