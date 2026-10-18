import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- A quadratic exponential remainder with the exact linear coefficient. -/
theorem exp_sub_one_quadratic (s : ℝ) (hs : 0 ≤ s) (hsmall : s ≤ 1 / 2) :
    0 ≤ Real.exp s - 1 ∧ Real.exp s - 1 ≤ s + 2 * s ^ 2 ∧
      Real.exp s - 1 ≤ 2 * s := by
  have he := Real.exp_bound_div_one_sub_of_interval hs (by linarith : s < 1)
  have hd : 0 < 1 - s := by linarith
  have hq : 1 / (1 - s) ≤ 1 + s + 2 * s ^ 2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (sq_nonneg s) (show 0 ≤ 1 - 2 * s by linarith)]
  have hlin : s + 2 * s ^ 2 ≤ 2 * s := by nlinarith
  exact ⟨sub_nonneg.mpr (Real.one_le_exp_iff.mpr hs), by linarith, by linarith⟩

/-- The rational generating bound preserves its first mean with a quadratic error. -/
theorem root_rational_quadratic_error (μ R s W : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hs : 0 ≤ s) (hW : 0 ≤ W) (hWlin : W ≤ 2 * s)
    (hWquad : W ≤ s + 2 * s ^ 2) (hsmall : R * W ≤ 1 / 2) :
    μ * W / (1 - R * W) ≤ μ * s + μ * (2 + 8 * R) * s ^ 2 := by
  have hd : 0 < 1 - R * W := by linarith
  have hf : μ * W / (1 - R * W) ≤ μ * W + 2 * μ * R * W ^ 2 := by
    apply (div_le_iff₀ hd).mpr
    have hh : 0 ≤ μ * R * W ^ 2 * (1 - 2 * (R * W)) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hsq : W ^ 2 ≤ 4 * s ^ 2 := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hWquad hμ
  have h₂ := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 * μ * R by positivity)
  nlinarith

/-- Logarithms of the geometric bound retain the exact linear mean term. -/
theorem root_log_generating_quadratic (μ R s : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hs : 0 ≤ s) (hsmall : s ≤ 1 / 2) (hRW : R * (Real.exp s - 1) ≤ 1 / 2) :
    Real.log (1 + μ * (Real.exp s - 1) / (1 - R * (Real.exp s - 1))) ≤
      μ * s + μ * (2 + 8 * R) * s ^ 2 := by
  obtain ⟨hW, hquad, hlin⟩ := exp_sub_one_quadratic s hs hsmall
  have hd : 0 < 1 - R * (Real.exp s - 1) := by linarith
  have hn : 0 ≤ μ * (Real.exp s - 1) / (1 - R * (Real.exp s - 1)) :=
    div_nonneg (mul_nonneg hμ hW) hd.le
  have hl := Real.log_le_sub_one_of_pos (show
    0 < 1 + μ * (Real.exp s - 1) / (1 - R * (Real.exp s - 1)) by linarith)
  have hf := root_rational_quadratic_error μ R s (Real.exp s - 1)
    hμ hR hs hW hlin hquad hRW
  linarith

/-- Any positive moment bounded by the geometric expression inherits the exact mean term. -/
theorem root_log_moment_from_generating (μ R s M : ℝ) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hs : 0 ≤ s) (hsmall : s ≤ 1 / 2) (hRs : R * s ≤ 1 / 4)
    (hM : 0 < M)
    (hbound : M ≤ 1 + μ * (Real.exp s - 1) / (1 - R * (Real.exp s - 1))) :
    Real.log M ≤ μ * s + μ * (2 + 8 * R) * s ^ 2 := by
  have hlin := (exp_sub_one_quadratic s hs hsmall).2.2
  have hh := mul_le_mul_of_nonneg_left hlin hR
  exact (Real.log_le_log hM hbound).trans
    (root_log_generating_quadratic μ R s hμ hR hs hsmall (by nlinarith))

end SRWTightness
