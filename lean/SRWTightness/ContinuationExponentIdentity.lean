import SRWTightness.SourceCoarseTime

namespace SRWTightness

/-- Equation (7.32), retaining the nonnegative continuation remainder exactly. -/
theorem continuation_exponent_identity (θ N ν x : ℝ) (h : N - ν ≠ 0) :
    (θ * N - x) ^ 2 / (2 * (N - ν)) =
      θ ^ 2 * N / 2 + θ ^ 2 * ν / 2 - θ * x +
        (θ * ν - x) ^ 2 / (2 * (N - ν)) := by
  field_simp
  <;> ring

/-- Dropping the square remainder gives the continuation exponent lower bound. -/
theorem continuation_exponent_lower (θ N ν x : ℝ) (h : 0 < N - ν) :
    θ ^ 2 * N / 2 + θ ^ 2 * ν / 2 - θ * x ≤
      (θ * N - x) ^ 2 / (2 * (N - ν)) := by
  rw [continuation_exponent_identity θ N ν x h.ne']
  have hh : 0 ≤ (θ * ν - x) ^ 2 / (2 * (N - ν)) := by positivity
  linarith

end SRWTightness
