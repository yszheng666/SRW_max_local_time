import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- The leading exponential cost in the upper terminal-block convolution, source (4.9). -/
theorem source_upper_gaussian_linear_square (a z v : ℝ) (hv : 0 < v) :
    -(a - z) ^ 2 / (2 * v) - 2 * z =
      -2 * a + 2 * v - (a - 2 * v - z) ^ 2 / (2 * v) := by
  field_simp
  <;> ring

/-- The two Gaussian costs in the terminal convolution retain a positive residual cost. -/
theorem source_upper_gaussian_double_square (ζ z v h c : ℝ)
    (hv : 0 < v) (hh : 0 < h) (hc : 0 < c) :
    (ζ - z) ^ 2 / (2 * v) + c * z ^ 2 / h =
      (h + 2 * c * v) / (2 * v * h) * (z - h * ζ / (h + 2 * c * v)) ^ 2 +
        c * ζ ^ 2 / (h + 2 * c * v) := by
  have hd : 0 < h + 2 * c * v := by positivity
  field_simp
  <;> ring

/-- Retain half the quadratic weight for integration while extracting a uniform cost. -/
theorem source_upper_gaussian_cost_lower (ζ z v h c : ℝ)
    (hv : 0 < v) (hh : 0 < h) (hc : 0 < c) :
    c * z ^ 2 / (2 * h) + c * ζ ^ 2 / (2 * (h + c * v)) ≤
      (ζ - z) ^ 2 / (2 * v) + c * z ^ 2 / h := by
  have he := source_upper_gaussian_double_square ζ z v h (c / 2) hv hh (by positivity)
  have hn : 0 ≤ (h + 2 * (c / 2) * v) / (2 * v * h) *
      (z - h * ζ / (h + 2 * (c / 2) * v)) ^ 2 := by positivity
  have hr : (c / 2) * ζ ^ 2 / (h + 2 * (c / 2) * v) =
      c * ζ ^ 2 / (2 * (h + c * v)) := by
    have hd : 0 < h + c * v := by positivity
    have hd' : 0 < h + 2 * (c / 2) * v := by positivity
    field_simp
    <;> ring
  rw [hr] at he
  have hz : c * z ^ 2 / h = (c / 2) * z ^ 2 / h + c * z ^ 2 / (2 * h) := by ring
  rw [hz]
  linarith only [he, hn]

/-- A Gaussian envelope with a separate terminal-height decay factor. -/
theorem source_upper_gaussian_exponential_bound (ζ z v h c : ℝ)
    (hv : 0 < v) (hh : 0 < h) (hc : 0 < c) :
    Real.exp (-((ζ - z) ^ 2 / (2 * v) + c * z ^ 2 / h)) ≤
      Real.exp (-(c * ζ ^ 2 / (2 * (h + c * v)))) *
        Real.exp (-(c * z ^ 2 / (2 * h))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb := source_upper_gaussian_cost_lower ζ z v h c hv hh hc
  linarith only [hb]

end SRWTightness
