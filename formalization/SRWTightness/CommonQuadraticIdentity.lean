import SRWTightness.SourceCommonPairEndpoint

namespace SRWTightness

/-- The exact denominator identity underlying the coarse-pair spatial exponent. -/
theorem common_quadratic_identity (θ T j v : ℝ) (hj : j ≠ 0) (hrem : T - j ≠ 0) :
    (θ * j + v) ^ 2 / (2 * j) + (θ * T - (θ * j + v)) ^ 2 / (T - j) =
      θ ^ 2 * (T - j / 2) - θ * v + v ^ 2 * (1 / (2 * j) + 1 / (T - j)) := by
  field_simp
  <;> ring

/-- Equation (9.12), with the actual source height, slope and coarse endpoint. -/
theorem source_common_quadratic_identity (t : ℝ) (j : ℕ)
    (hT : sourceTotalTime t ≠ 0) (hj : 0 < j)
    (hrem : sourceTotalTime t - (j : ℝ) ≠ 0) :
    let v := 4 - (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)
    sourceCommonPairEndpoint t j ^ 2 / (2 * (j : ℝ)) +
      (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 /
        (sourceTotalTime t - j) =
      sourceBarrierSlope t ^ 2 * (sourceTotalTime t - (j : ℝ) / 2) -
        sourceBarrierSlope t * v + v ^ 2 * (1 / (2 * (j : ℝ)) +
          1 / (sourceTotalTime t - j)) := by
  have hy : sourceTerminalHeight t = sourceBarrierSlope t * sourceTotalTime t := by
    simp [sourceBarrierSlope, hT]
  have hb : sourceCommonPairEndpoint t j = sourceBarrierSlope t * j +
      (4 - (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) := by
    unfold sourceCommonPairEndpoint
    ring
  dsimp only
  rw [hb, hy]
  exact common_quadratic_identity _ _ _ _ (by exact_mod_cast hj.ne') hrem

end SRWTightness
