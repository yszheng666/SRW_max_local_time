import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace SRWTightness

/-- A stable denominator retains the leading coefficient one in a root mean. -/
theorem root_mean_ratio_error (g α d u v : ℝ) (hg : 0 < g)
    (hd : g / 2 ≤ d) (hu : |α - g| ≤ u) (hv : |d - g| ≤ v) :
    |α / d - 1| ≤ (2 / g) * (u + v) := by
  have hd0 : 0 < d := by linarith
  have hnum : |α - d| ≤ u + v := by
    calc
      _ = |(α - g) + (g - d)| := by congr 1; ring
      _ ≤ |α - g| + |g - d| := abs_add_le _ _
      _ ≤ u + v := by rw [abs_sub_comm g d]; exact add_le_add hu hv
  have hsum : 0 ≤ u + v := (abs_nonneg _).trans hnum
  have heq : α / d - 1 = (α - d) / d := by field_simp
  rw [heq, abs_div, abs_of_pos hd0]
  calc
    _ ≤ (u + v) / d := div_le_div_of_nonneg_right hnum hd0.le
    _ ≤ (u + v) / (g / 2) := div_le_div_of_nonneg_left hsum (by positivity) hd
    _ = (2 / g) * (u + v) := by ring

/-- Summing two means preserves the exact leading coefficient two without independence. -/
theorem root_pair_mean_ratio_error (g α d₁ d₂ u v₁ v₂ : ℝ) (hg : 0 < g)
    (hd₁ : g / 2 ≤ d₁) (hd₂ : g / 2 ≤ d₂)
    (hu : |α - g| ≤ u) (hv₁ : |d₁ - g| ≤ v₁) (hv₂ : |d₂ - g| ≤ v₂) :
    |α * (d₁⁻¹ + d₂⁻¹) - 2| ≤ (2 / g) * (2 * u + v₁ + v₂) := by
  calc
    _ = |(α / d₁ - 1) + (α / d₂ - 1)| := by congr 1; simp only [div_eq_mul_inv]; ring
    _ ≤ |α / d₁ - 1| + |α / d₂ - 1| := abs_add_le _ _
    _ ≤ (2 / g) * (u + v₁) + (2 / g) * (u + v₂) :=
      add_le_add (root_mean_ratio_error g α d₁ u v₁ hg hd₁ hu hv₁)
        (root_mean_ratio_error g α d₂ u v₂ hg hd₂ hu hv₂)
    _ = _ := by ring

end SRWTightness
