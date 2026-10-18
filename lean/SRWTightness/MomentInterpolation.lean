import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory

namespace SRWTightness

/-- A polynomial proof of the L1/L2/L4 interpolation inequality used in the one-sided comparison. -/
theorem moment_two_cubed_le_abs_one_sq_four {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Integrable X μ)
    (h2 : Integrable (fun ω ↦ (X ω) ^ 2) μ) (h4 : Integrable (fun ω ↦ (X ω) ^ 4) μ)
    (hp2 : 0 < ∫ ω, (X ω) ^ 2 ∂μ) (hp4 : 0 < ∫ ω, (X ω) ^ 4 ∂μ) :
    (∫ ω, (X ω) ^ 2 ∂μ) ^ 3 ≤
      (∫ ω, |X ω| ∂μ) ^ 2 * (∫ ω, (X ω) ^ 4 ∂μ) := by
  let m1 := ∫ ω, |X ω| ∂μ
  let m2 := ∫ ω, (X ω) ^ 2 ∂μ
  let m4 := ∫ ω, (X ω) ^ 4 ∂μ
  let a := Real.sqrt (m4 / m2)
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos hp4 hp2)
  have ha2 : a ^ 2 * m2 = m4 := by
    dsimp [a]
    rw [Real.sq_sqrt (div_pos hp4 hp2).le]
    exact div_mul_cancel₀ m4 (ne_of_gt hp2)
  have hpoint (ω : Ω) : 3 * a ^ 2 * (X ω) ^ 2 ≤ 2 * a ^ 3 * |X ω| + (X ω) ^ 4 := by
    have hn : 0 ≤ |X ω| * (|X ω| - a) ^ 2 * (|X ω| + 2 * a) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (by positivity)
    have hs : |X ω| ^ 2 = (X ω) ^ 2 := sq_abs _
    have hfour : |X ω| ^ 4 = (X ω) ^ 4 := by
      calc
        _ = (|X ω| ^ 2) ^ 2 := by ring
        _ = ((X ω) ^ 2) ^ 2 := by rw [hs]
        _ = _ := by ring
    have hid : |X ω| * (|X ω| - a) ^ 2 * (|X ω| + 2 * a) =
        |X ω| ^ 4 - 3 * a ^ 2 * |X ω| ^ 2 + 2 * a ^ 3 * |X ω| := by ring
    rw [hid, hs, hfour] at hn
    linarith
  have hl : Integrable (fun ω ↦ 3 * a ^ 2 * (X ω) ^ 2) μ := h2.const_mul _
  have hr : Integrable (fun ω ↦ 2 * a ^ 3 * |X ω| + (X ω) ^ 4) μ :=
    (hX.abs.const_mul _).add h4
  have hi := integral_mono hl hr hpoint
  rw [integral_const_mul, integral_add (hX.abs.const_mul _) h4, integral_const_mul] at hi
  change 3 * a ^ 2 * m2 ≤ 2 * a ^ 3 * m1 + m4 at hi
  have hm1 : 0 ≤ m1 := integral_nonneg (fun ω ↦ abs_nonneg _)
  have hb : m2 ≤ a * m1 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ha)).mp
    nlinarith [ha2]
  have hc : m2 ^ 2 ≤ a ^ 2 * m1 ^ 2 := by nlinarith [mul_nonneg ha.le hm1]
  change m2 ^ 3 ≤ m1 ^ 2 * m4
  nlinarith [mul_le_mul_of_nonneg_right hc hp2.le]

end SRWTightness
