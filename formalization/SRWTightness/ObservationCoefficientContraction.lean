import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace SRWTightness

/-- Combining probability-weighted observations never increases the sum of absolute coefficients. -/
theorem observation_coefficients_l1 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → κ → ℝ) (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (β : ι → ℝ) :
    (∑ z, |∑ i, β i * w i z|) ≤ ∑ i, |β i| := by
  calc
    _ ≤ ∑ z, ∑ i, |β i * w i z| :=
      Finset.sum_le_sum (fun z _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, ∑ z, |β i| * w i z := by
      simp only [abs_mul, abs_of_nonneg (hw _ _)]
      exact Finset.sum_comm
    _ = _ := by simp only [← Finset.mul_sum, hw1, mul_one]

/-- Dividing the combined physical coefficients by a positive scale preserves the l1 bound. -/
theorem normalized_observation_coefficients_l1 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → κ → ℝ) (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (β : ι → ℝ) (c : ℝ) (hc : 0 < c) :
    (∑ z, |(∑ i, β i * w i z) / c|) ≤ (∑ i, |β i|) / c := by
  simp only [abs_div, abs_of_pos hc, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right (observation_coefficients_l1 w hw hw1 β) hc.le

/-- Collapsing an observation family gives exactly the physical coefficient vector. -/
theorem observation_linear_combination {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → κ → ℝ) (β : ι → ℝ) (Y : κ → ℝ) :
    (∑ i, β i * ∑ z, w i z * Y z) = ∑ z, (∑ i, β i * w i z) * Y z := by
  simp only [Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  exact Finset.sum_comm

end SRWTightness
