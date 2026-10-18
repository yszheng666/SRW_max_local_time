import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace SRWTightness

theorem inverse_radius_denominator_positive (x y s : ℝ) (hs : s = x ^ 2 + y ^ 2)
    (hlarge : 4 ≤ s) :
    0 < s + 1 + 2 * x ∧ 0 < s + 1 - 2 * x ∧
    0 < s + 1 + 2 * y ∧ 0 < s + 1 - 2 * y := by
  have hx := sq_nonneg (x - 2)
  have hxn := sq_nonneg (x + 2)
  have hy := sq_nonneg (y - 2)
  have hyn := sq_nonneg (y + 2)
  have hx0 := sq_nonneg x
  have hy0 := sq_nonneg y
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem inverse_radius_product_bound (x y s : ℝ) (hs : s = x ^ 2 + y ^ 2)
    (hlarge : 1 ≤ s) :
    ((s + 1) ^ 2 - 4 * x ^ 2) * ((s + 1) ^ 2 - 4 * y ^ 2) ≤
      s * (s + 1) * (s ^ 2 + 1) := by
  have hxy : 16 * x ^ 2 * y ^ 2 ≤ 4 * s ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  have hp : 0 ≤ (s - 1) * (s ^ 2 + 1) :=
    mul_nonneg (sub_nonneg.mpr hlarge) (by nlinarith [sq_nonneg s])
  have he : s * (s + 1) * (s ^ 2 + 1) -
      ((s + 1) ^ 2 - 4 * x ^ 2) * ((s + 1) ^ 2 - 4 * y ^ 2) =
      (s - 1) * (s ^ 2 + 1) + 4 * s ^ 2 - 16 * x ^ 2 * y ^ 2 := by
    rw [hs]
    ring
  linarith

/-- The inverse squared radius is subharmonic outside a fixed disk, by exact algebra. -/
theorem inverse_radius_submean (x y s : ℝ) (hs : s = x ^ 2 + y ^ 2)
    (hlarge : 4 ≤ s) :
    1 / s ≤ (1 / (s + 1 + 2 * x) + 1 / (s + 1 - 2 * x) +
      1 / (s + 1 + 2 * y) + 1 / (s + 1 - 2 * y)) / 4 := by
  obtain ⟨hxp, hxm, hyp, hym⟩ := inverse_radius_denominator_positive x y s hs hlarge
  have hspos : 0 < s := by linarith
  have hp := inverse_radius_product_bound x y s hs (by linarith)
  have he : (1 / (s + 1 + 2 * x) + 1 / (s + 1 - 2 * x) +
      1 / (s + 1 + 2 * y) + 1 / (s + 1 - 2 * y)) / 4 =
      ((s + 1) * (s ^ 2 + 1)) /
        (((s + 1) ^ 2 - 4 * x ^ 2) * ((s + 1) ^ 2 - 4 * y ^ 2)) := by
    have hA : (s + 1) ^ 2 - 4 * x ^ 2 = (s + 1 + 2 * x) * (s + 1 - 2 * x) := by ring
    have hB : (s + 1) ^ 2 - 4 * y ^ 2 = (s + 1 + 2 * y) * (s + 1 - 2 * y) := by ring
    rw [hA, hB]
    field_simp
    nlinarith [hs]
  have hden : 0 < ((s + 1) ^ 2 - 4 * x ^ 2) * ((s + 1) ^ 2 - 4 * y ^ 2) := by
    have hA : 0 < (s + 1) ^ 2 - 4 * x ^ 2 := by nlinarith [mul_pos hxp hxm]
    have hB : 0 < (s + 1) ^ 2 - 4 * y ^ 2 := by nlinarith [mul_pos hyp hym]
    exact mul_pos hA hB
  rw [he]
  apply (div_le_div_iff₀ hspos hden).mpr
  nlinarith [hp]

end SRWTightness
