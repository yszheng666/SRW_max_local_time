import SRWTightness.SourceDeficitBand

namespace SRWTightness

/-- Exact shifted coarse exponent in the one-point calculation. -/
theorem source_coarse_exponent_shift (t q : ℝ)
    (hN : (sourceCoarseGeneration t : ℝ) ≠ 0) :
    sourceTerminalRoot t q ^ 2 / (2 * (sourceCoarseGeneration t : ℝ)) =
      (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) ^ 2 /
        (2 * (sourceCoarseGeneration t : ℝ)) - sourceBarrierSlope t * q +
          q ^ 2 / (2 * (sourceCoarseGeneration t : ℝ)) := by
  unfold sourceTerminalRoot
  field_simp
  <;> ring

/-- Multiplication by the terminal tilt cancels the leading deficit exponential. -/
theorem source_coarse_terminal_exponential (t q : ℝ)
    (hN : (sourceCoarseGeneration t : ℝ) ≠ 0) :
    Real.exp (-(sourceTerminalRoot t q ^ 2 /
      (2 * (sourceCoarseGeneration t : ℝ)))) *
        Real.exp (-2 * sourceLowerTime (sourceLowerRadius t) - 2 * q) =
      Real.exp (-((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) ^ 2 /
        (2 * (sourceCoarseGeneration t : ℝ))) -
          2 * sourceLowerTime (sourceLowerRadius t)) *
        Real.exp ((sourceBarrierSlope t - 2) * q -
          q ^ 2 / (2 * (sourceCoarseGeneration t : ℝ))) := by
  rw [← Real.exp_add, ← Real.exp_add, source_coarse_exponent_shift t q hN]
  congr 1
  ring

/-- Uniform control of the exponent left after the coarse/terminal cancellation. -/
theorem coarse_terminal_exponent_error (θ q d N : ℝ)
    (hN : 0 < N) (hd : 1 ≤ d) (hq : 0 ≤ q) (hq' : q ≤ 2 * Real.sqrt d) :
    |(θ - 2) * q - q ^ 2 / (2 * N)| ≤
      2 * |θ - 2| * d + 2 * d / N := by
  have hd0 : 0 ≤ d := by linarith
  have hs := Real.sq_sqrt hd0
  have hs0 := Real.sqrt_nonneg d
  have hsd : Real.sqrt d ≤ d := by nlinarith
  have hq2 : q ^ 2 ≤ 4 * d := by nlinarith
  calc
    _ ≤ |(θ - 2) * q| + |q ^ 2 / (2 * N)| := abs_sub _ _
    _ = |θ - 2| * q + q ^ 2 / (2 * N) := by
      rw [abs_mul, abs_of_nonneg hq,
        abs_of_nonneg (show 0 ≤ q ^ 2 / (2 * N) by positivity)]
    _ ≤ |θ - 2| * (2 * d) + (4 * d) / (2 * N) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
        (div_le_div_of_nonneg_right hq2 (by positivity))
    _ = _ := by ring

end SRWTightness
