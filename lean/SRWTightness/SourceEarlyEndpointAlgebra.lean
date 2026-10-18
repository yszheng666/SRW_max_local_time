import SRWTightness.EarlyPopulationEndpoint

namespace SRWTightness

/-- Equation 8.25, including its nonpositive square remainder. -/
theorem source_early_endpoint_quadratic_identity (j : ℕ) (w : ℝ) :
    -(2 * (j : ℝ) - w + 4) ^ 2 / (2 * ((j : ℝ) + 1)) +
        4 * (2 * (j : ℝ) - w + 4) =
      6 * (j : ℝ) - 2 * w + 10 - (w - 2) ^ 2 / (2 * ((j : ℝ) + 1)) := by
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

end SRWTightness
