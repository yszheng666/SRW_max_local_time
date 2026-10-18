import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Exact occupation-window threshold, with an explicitly rounded visit-count cutoff. -/
noncomputable def terminalOccupationThreshold (cutoff α g u : ℝ) : ℝ :=
  (cutoff - α * (u ^ 2 / 2)) / (u * Real.sqrt (α * g))

theorem terminalThreshold_sqrt_bounds (α g : ℝ) (hg : 0 < g) (hα : g ≤ α) :
    g ≤ Real.sqrt (α * g) ∧ Real.sqrt (α * g) ≤ α := by
  have ha : 0 < α := hg.trans_le hα
  have hs := Real.sq_sqrt (show 0 ≤ α * g by positivity)
  have hnon := Real.sqrt_nonneg (α * g)
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hα) hg.le,
    mul_nonneg (sub_nonneg.mpr hα) ha.le]

/-- Separate rounding and reference-intensity errors from the ideal square-difference threshold. -/
theorem terminalThreshold_error_identity (cutoff α g u y : ℝ)
    (hg : 0 < g) (hα : g ≤ α) (hu : 0 < u) :
    terminalOccupationThreshold cutoff α g u - (y ^ 2 - u ^ 2) / (2 * u) =
      (cutoff - g * y ^ 2 / 2) / (u * Real.sqrt (α * g)) +
      (g - Real.sqrt (α * g)) * y ^ 2 / (2 * u * Real.sqrt (α * g)) +
      (Real.sqrt (α * g) - α) * u / (2 * Real.sqrt (α * g)) := by
  have hs : 0 < Real.sqrt (α * g) := hg.trans_le (terminalThreshold_sqrt_bounds α g hg hα).1
  unfold terminalOccupationThreshold
  field_simp
  <;> ring

/-- A unit rounding error and an intensity perturbation give an explicit threshold error. -/
theorem terminalThreshold_error_bound (cutoff α g u y : ℝ)
    (hg : 0 < g) (hα : g ≤ α) (hu : 0 < u)
    (hround : 0 ≤ cutoff - g * y ^ 2 / 2)
    (hround1 : cutoff - g * y ^ 2 / 2 ≤ 1) :
    |terminalOccupationThreshold cutoff α g u - (y ^ 2 - u ^ 2) / (2 * u)| ≤
      1 / (u * g) + (α - g) * (y ^ 2 + u ^ 2) / (2 * u * g) := by
  let s := Real.sqrt (α * g)
  have hb := terminalThreshold_sqrt_bounds α g hg hα
  have hs : 0 < s := hg.trans_le hb.1
  have h1 : |(cutoff - g * y ^ 2 / 2) / (u * s)| ≤ 1 / (u * g) := by
    rw [abs_of_nonneg (div_nonneg hround (by positivity))]
    exact (div_le_div_of_nonneg_right hround1 (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hb.1 hu.le))
  have h2 : |(g - s) * y ^ 2 / (2 * u * s)| ≤ (α - g) * y ^ 2 / (2 * u * g) := by
    rw [abs_div, abs_mul, abs_of_nonpos (sub_nonpos.mpr hb.1),
      abs_of_nonneg (sq_nonneg y), abs_of_pos (by positivity : 0 < 2 * u * s)]
    have hn : -(g - s) * y ^ 2 ≤ (α - g) * y ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hb.2]) (sq_nonneg y)
    exact (div_le_div_of_nonneg_right hn (by positivity)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hb.1 (by positivity)))
  have h3 : |(s - α) * u / (2 * s)| ≤ (α - g) * u / (2 * g) := by
    rw [abs_div, abs_mul, abs_of_nonpos (sub_nonpos.mpr hb.2),
      abs_of_pos hu, abs_of_pos (by positivity : 0 < 2 * s)]
    have hn : -(s - α) * u ≤ (α - g) * u :=
      mul_le_mul_of_nonneg_right (by linarith [hb.1]) hu.le
    exact (div_le_div_of_nonneg_right hn (by positivity)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hb.1 (by norm_num)))
  rw [terminalThreshold_error_identity cutoff α g u y hg hα hu]
  calc
    _ ≤ (|(cutoff - g * y ^ 2 / 2) / (u * s)| +
        |(g - s) * y ^ 2 / (2 * u * s)|) + |(s - α) * u / (2 * s)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ (1 / (u * g) + (α - g) * y ^ 2 / (2 * u * g)) + (α - g) * u / (2 * g) :=
      add_le_add (add_le_add h1 h2) h3
    _ = _ := by field_simp; ring

end SRWTightness
