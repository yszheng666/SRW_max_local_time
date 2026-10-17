import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace SRWTightness

/-- Capacity normalization converts swept exponential bounds into bounds for each atom. -/
theorem normalized_sweep_bounds (α cap p e C : ℝ) (hα : 0 ≤ α) (hp : 0 ≤ p)
    (hcap : 1 / 2 ≤ α * cap ∧ α * cap ≤ 2)
    (hs : Real.exp (-C) * cap * p ≤ e ∧ e ≤ Real.exp C * cap * p) :
    (Real.exp (-C) / 2) * (α * e) ≤ p ∧ p ≤ (2 * Real.exp C) * (α * e) := by
  have heU : α * e ≤ (2 * Real.exp C) * p := by
    calc
      _ ≤ α * (Real.exp C * cap * p) := mul_le_mul_of_nonneg_left hs.2 hα
      _ = (Real.exp C * (α * cap)) * p := by ring
      _ ≤ (Real.exp C * 2) * p := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcap.2 (Real.exp_nonneg C)) hp
      _ = _ := by ring
  have heL : ((1 / 2) * Real.exp (-C)) * p ≤ α * e := by
    calc
      _ = (Real.exp (-C) * (1 / 2)) * p := by ring
      _ ≤ (Real.exp (-C) * (α * cap)) * p := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcap.1 (Real.exp_nonneg (-C))) hp
      _ = α * (Real.exp (-C) * cap * p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs.1 hα
  have hi : (Real.exp (-C) / 2) * (2 * Real.exp C) = 1 := by
    rw [Real.exp_neg]
    field_simp
  have hj : (2 * Real.exp C) * ((1 / 2) * Real.exp (-C)) = 1 := by
    rw [Real.exp_neg]
    field_simp
  constructor
  · have h := mul_le_mul_of_nonneg_left heU (by positivity : 0 ≤ Real.exp (-C) / 2)
    simpa only [← mul_assoc, hi, one_mul] using h
  · have h := mul_le_mul_of_nonneg_left heL (by positivity : 0 ≤ 2 * Real.exp C)
    simpa only [← mul_assoc, hj, one_mul] using h

end SRWTightness
