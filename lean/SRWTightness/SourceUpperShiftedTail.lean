import SRWTightness.SourceUpperVisitThreshold
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds

namespace SRWTightness

/-- The Gaussian height exponent dominates the desired disk-tail exponent. -/
theorem source_upper_height_exponent_ge : (3 : ℝ) / 2 ≤ 2 * Real.sqrt Real.pi := by
  have hp := Real.pi_gt_three
  have hs := Real.sq_sqrt Real.pi_pos.le
  have hn := Real.sqrt_nonneg Real.pi
  nlinarith

/-- A fixed nonnegative shift is absorbed in the constant of the slower exponential tail. -/
theorem source_upper_shifted_tail_bound (d s : ℝ) (hd : 0 ≤ d) (hs : d ≤ s) :
    (1 + (s - d)) * Real.exp (-(2 * Real.sqrt Real.pi * (s - d))) +
      Real.exp (-3 * (s - d) / 2) ≤
        (2 * Real.exp (3 * d / 2)) * (1 + s) * Real.exp (-3 * s / 2) := by
  have hu : 0 ≤ s - d := sub_nonneg.mpr hs
  have hs0 : 0 ≤ s := hd.trans hs
  have hexp : Real.exp (-(2 * Real.sqrt Real.pi * (s - d))) ≤
      Real.exp (-3 * (s - d) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr source_upper_height_exponent_ge) hu]
  have hfirst : (1 + (s - d)) * Real.exp (-(2 * Real.sqrt Real.pi * (s - d))) ≤
      (1 + s) * Real.exp (-3 * (s - d) / 2) :=
    mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by linarith)
  have hsecond : Real.exp (-3 * (s - d) / 2) ≤
      (1 + s) * Real.exp (-3 * (s - d) / 2) := by
    nlinarith [mul_nonneg hs0 (Real.exp_pos (-3 * (s - d) / 2)).le]
  have he : Real.exp (-3 * (s - d) / 2) =
      Real.exp (3 * d / 2) * Real.exp (-3 * s / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh := add_le_add hfirst hsecond
  rw [he] at hh
  nlinarith

end SRWTightness
