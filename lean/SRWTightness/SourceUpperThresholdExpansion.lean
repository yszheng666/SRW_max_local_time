import SRWTightness.SourceUpperTerminalHeightPerturbation

namespace SRWTightness

/-- Exact separation of rounding, slope and mark-normalization errors in source (4.10). -/
theorem source_upper_threshold_identity (a b u y θ N d x q : ℝ)
    (hy : y = θ * (N + d)) (hx : x = θ * N) (hq : q = x - u) :
    a - b * u = 2 * d + q + (a - y + (θ - 2) * d + (1 - b) * u) := by
  rw [hy, hq, hx]
  ring

/-- The source threshold error is controlled by its three distinct contributions. -/
theorem source_upper_threshold_error_bound (a b u y θ d E₁ E₂ E₃ U : ℝ)
    (hd : 0 ≤ d) (ha : |a - y| ≤ E₁) (hθ : |θ - 2| ≤ E₂)
    (hb : |b - 1| ≤ E₃) (hu : |u| ≤ U) :
    |a - y + (θ - 2) * d + (1 - b) * u| ≤ E₁ + E₂ * d + E₃ * U := by
  have h₂ : |(θ - 2) * d| ≤ E₂ * d := by
    rw [abs_mul, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_right hθ hd
  have h₃ : |(1 - b) * u| ≤ E₃ * U := by
    rw [abs_mul, abs_sub_comm 1 b]
    exact mul_le_mul hb hu (abs_nonneg _) ((abs_nonneg _).trans hb)
  have ht := abs_add_le (a - y + (θ - 2) * d) ((1 - b) * u)
  have ht' := abs_add_le (a - y) ((θ - 2) * d)
  linarith

end SRWTightness
