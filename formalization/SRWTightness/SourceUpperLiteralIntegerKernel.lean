import SRWTightness.SourceUpperIntegerWindowKernel
import SRWTightness.SourceUpperFineDepthRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

namespace SRWTightness

/-- The exact S(q)=1+A+2d^(1/4)+q factor in the original integer Gaussian summand. -/
noncomputable def sourceUpperLiteralIntegerKernel (t s c L : ℝ) (z : ℤ) : ℝ :=
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  ((1 + (4 + s) + 2 * d ^ (1 / 4 : ℝ)) + z) / d *
    (1 + max (z : ℝ) 0 / Real.sqrt d) *
      Real.exp (-(x - z) ^ 2 / (2 * L) - 2 * z - c * (max (z : ℝ) 0) ^ 2 / d)

/-- At admissible integer deficits, the fixed slack enlargement costs at most a factor four. -/
theorem source_upper_literal_integer_kernel_bounds (t s c L : ℝ) (z : ℤ)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hr : 3 ≤ upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ))
    (hz : -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
      (z : ℝ)) :
    0 ≤ sourceUpperLiteralIntegerKernel t s c L z ∧
      sourceUpperLiteralIntegerKernel t s c L z ≤ sourceUpperIntegerWindowKernel t s c L z ∧
      sourceUpperIntegerWindowKernel t s c L z ≤ 4 * sourceUpperLiteralIntegerKernel t s c L z := by
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  let S := 1 + (4 + s) + 2 * d ^ (1 / 4 : ℝ) + (z : ℝ)
  let V := (1 + max (z : ℝ) 0 / Real.sqrt d) *
    Real.exp (-(x - z) ^ 2 / (2 * L) - 2 * z - c * (max (z : ℝ) 0) ^ 2 / d) / d
  have hS : 1 ≤ S := by dsimp [S, d]; linarith
  have hV : 0 ≤ V := by dsimp [V, d]; positivity
  have he : sourceUpperLiteralIntegerKernel t s c L z = S * V := by
    dsimp [sourceUpperLiteralIntegerKernel, S, V, x, d]
    ring
  have ho : sourceUpperIntegerWindowKernel t s c L z = (S + 3) * V := by
    dsimp [sourceUpperIntegerWindowKernel, S, V, x, d]
    ring
  rw [he, ho]
  refine ⟨mul_nonneg (by linarith) hV, mul_le_mul_of_nonneg_right (by linarith) hV, ?_⟩
  exact (mul_le_mul_of_nonneg_right (show S + 3 ≤ 4 * S by linarith) hV).trans_eq (by ring)

/-- Actual terminal quarter-depth eventually makes the literal S(q) uniformly positive. -/
theorem source_upper_terminal_quarter_depth_eventually :
    ∀ᶠ t : ℝ in atTop, 3 ≤ upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) :=
  ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp
    source_upper_depth_tendsto_internal).eventually (eventually_ge_atTop 3)

end SRWTightness
