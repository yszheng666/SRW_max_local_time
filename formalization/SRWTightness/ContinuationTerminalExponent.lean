import SRWTightness.SourceContinuationRange

namespace SRWTightness

/-- The terminal deficit cancels the linear window exponent uniformly in the early range. -/
theorem continuation_terminal_exponent (t L N ν θ x q d : ℝ)
    (ht : 0 < t) (hL : t / 2 ≤ L) (hN : ν + L = N)
    (hν0 : 0 ≤ ν) (hν : ν ≤ d) (hθ : θ ≤ 2) (hx : 0 ≤ x)
    (hq0 : 0 ≤ q) (hq : q ≤ 2 * d) (hd : 8 * d ^ 2 ≤ t) :
    -((x - (θ * N - q)) ^ 2 / (2 * L)) - 2 * q ≤
      -((θ * N - x) ^ 2 / (2 * L)) + 1 := by
  have hL0 : 0 < L := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hθN := mul_le_mul_of_nonneg_right hθ hN0
  have hz : θ * N - x - 2 * L ≤ 2 * ν := by linarith
  have hzq := mul_le_mul_of_nonneg_right hz hq0
  have hnq : ν * q ≤ 2 * d ^ 2 := by
    have hh := mul_le_mul hν hq hq0 (show 0 ≤ d by linarith)
    nlinarith
  have hnum : (θ * N - x) ^ 2 - (x - (θ * N - q)) ^ 2 - 4 * L * q ≤ 2 * L := by
    nlinarith [sq_nonneg q]
  have hh : ((θ * N - x) ^ 2 - (x - (θ * N - q)) ^ 2 - 4 * L * q) /
      (2 * L) ≤ 1 := by
    apply (div_le_iff₀ (show 0 < 2 * L by positivity)).mpr
    simpa using hnum
  have he : ((θ * N - x) ^ 2 - (x - (θ * N - q)) ^ 2 - 4 * L * q) / (2 * L) =
      (θ * N - x) ^ 2 / (2 * L) - (x - (θ * N - q)) ^ 2 / (2 * L) - 2 * q := by
    field_simp
    <;> ring
  rw [he] at hh
  linarith

end SRWTightness
