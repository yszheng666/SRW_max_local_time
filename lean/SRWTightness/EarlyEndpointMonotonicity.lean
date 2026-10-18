import SRWTightness.SourceEarlyEndpointAlgebra

namespace SRWTightness

/-- The endpoint exponent increases up to its quadratic maximum. -/
theorem early_endpoint_quadratic_mono (d b c : ℝ) (hd : 0 < d)
    (hbc : b ≤ c) (hc : c ≤ 4 * d) :
    -b ^ 2 / (2 * d) + 4 * b ≤ -c ^ 2 / (2 * d) + 4 * c := by
  have hh : 0 ≤ (c - b) * (8 * d - c - b) :=
    mul_nonneg (sub_nonneg.mpr hbc) (by linarith only [hbc, hc])
  calc
    _ = (8 * d * b - b ^ 2) / (2 * d) := by field_simp; ring
    _ ≤ (8 * d * c - c ^ 2) / (2 * d) :=
      div_le_div_of_nonneg_right (by nlinarith only [hh]) (by positivity)
    _ = _ := by field_simp; ring

/-- The spatial count and continuation exponent cancel the leading early population growth. -/
theorem early_distance_exponent_cancellation (a J : ℕ) (hJ : J ≤ a) :
    -2 * (a : ℝ) - 4 * ((a + J + 5 : ℕ) : ℝ) + 6 * ((a - J : ℕ) : ℝ) =
      -10 * (J : ℝ) - 20 := by
  rw [Nat.cast_sub hJ]
  push_cast
  ring

end SRWTightness
