import SRWTightness.SourceUpperVisitThreshold
import SRWTightness.DiskOnePointLogTail

namespace SRWTightness

/-- Completing the square gives a uniform lower bound even when the height shift changes sign. -/
theorem upper_one_point_square_quotient (t x a : ℝ) (ht : 1 ≤ t) (ha : 0 ≤ a) :
    2 * t + 2 * x - a - Real.pi ≤ ((2 * t + x) ^ 2 - Real.pi) / (2 * t + a) := by
  have hd : 0 < 2 * t + a := by linarith
  have hdp : 0 ≤ Real.pi * (2 * t + a - 1) :=
    mul_nonneg Real.pi_pos.le (by linarith)
  apply (le_div_iff₀ hd).mpr
  nlinarith [sq_nonneg (x - a)]

/-- The source integer cutoff retains the full height exponent in the one-point geometric tail. -/
theorem source_upper_one_point_exponent (t s : ℝ) (ht : 1 ≤ t) :
    2 * t - 2 * Real.log t + 2 * Real.sqrt Real.pi * s -
        (Real.pi * diskDiagonalError + Real.pi) ≤
      ((sourceUpperVisitCutoff t s - 1 : ℕ) : ℝ) /
        ((2 / Real.pi) * t + diskDiagonalError) := by
  have hπ := Real.pi_pos
  have hD := diskDiagonalError_pos
  have hd : 0 < (2 / Real.pi) * t + diskDiagonalError := by positivity
  have hd' : 0 < 2 * t + Real.pi * diskDiagonalError := by positivity
  have hc := Nat.le_ceil (sourceUpperHeight t s ^ 2 / Real.pi)
  change sourceUpperHeight t s ^ 2 / Real.pi ≤ (sourceUpperVisitCutoff t s : ℝ) at hc
  have hn : (sourceUpperVisitCutoff t s : ℝ) ≤
      ((sourceUpperVisitCutoff t s - 1 : ℕ) : ℝ) + 1 := by
    have hh : sourceUpperVisitCutoff t s ≤ (sourceUpperVisitCutoff t s - 1) + 1 := by omega
    exact_mod_cast hh
  have hnum : sourceUpperHeight t s ^ 2 - Real.pi ≤
      Real.pi * ((sourceUpperVisitCutoff t s - 1 : ℕ) : ℝ) := by
    have hh := (div_le_iff₀ hπ).mp (hc.trans hn)
    nlinarith
  have hh := upper_one_point_square_quotient t
    (-Real.log t + Real.sqrt Real.pi * s) (Real.pi * diskDiagonalError) ht (by positivity)
  have heq : ((sourceUpperVisitCutoff t s - 1 : ℕ) : ℝ) /
      ((2 / Real.pi) * t + diskDiagonalError) =
      (Real.pi * ((sourceUpperVisitCutoff t s - 1 : ℕ) : ℝ)) /
        (2 * t + Real.pi * diskDiagonalError) := by
    field_simp
    <;> ring
  rw [heq]
  apply le_trans _ (div_le_div_of_nonneg_right hnum hd'.le)
  convert hh using 1 <;> first | rfl | (solve | ring) | (simp only [sourceUpperHeight]; ring)

/-- The actual one-point exponential factor is bounded by the source radius and height factors. -/
theorem source_upper_one_point_exponential (t s : ℝ) (ht : 1 ≤ t) :
    Real.exp (-((sourceUpperVisitCutoff t s - 1 : ℕ) : ℝ) /
      ((2 / Real.pi) * t + diskDiagonalError)) ≤
      Real.exp (Real.pi * diskDiagonalError + Real.pi) * t ^ 2 *
        Real.exp (-2 * t) * Real.exp (-(2 * Real.sqrt Real.pi * s)) := by
  have hh := source_upper_one_point_exponent t s ht
  have ht0 : 0 < t := by linarith
  calc
    _ ≤ Real.exp ((Real.pi * diskDiagonalError + Real.pi) +
        2 * Real.log t + (-2 * t) + (-(2 * Real.sqrt Real.pi * s))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith
    _ = _ := by
      rw [show 2 * Real.log t = Real.log t + Real.log t by ring]
      simp only [Real.exp_add, Real.exp_log ht0]
      ring

end SRWTightness
