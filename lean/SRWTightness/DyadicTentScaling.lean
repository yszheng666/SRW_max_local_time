import SRWTightness.SchauderTent
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field

namespace SRWTightness

noncomputable def dyadicTent (n k : ℕ) (t : ℝ) : ℝ :=
  scaledSchauderTent ((2 : ℝ) ^ n) k ((Real.sqrt 2)⁻¹ ^ n) t

theorem dyadicTent_left_scale (n k : ℕ) (t : ℝ) :
    dyadicTent (n + 1) k t = (Real.sqrt 2)⁻¹ * dyadicTent n k (2 * t) := by
  unfold dyadicTent scaledSchauderTent
  rw [pow_succ, pow_succ]
  have h : (2 : ℝ) ^ n * 2 * t - k = (2 : ℝ) ^ n * (2 * t) - k := by ring
  rw [h]
  ring

theorem dyadicTent_right_scale (n k : ℕ) (t : ℝ) :
    dyadicTent (n + 1) (k + 2 ^ n) t =
      (Real.sqrt 2)⁻¹ * dyadicTent n k (2 * t - 1) := by
  unfold dyadicTent scaledSchauderTent
  push_cast
  rw [pow_succ, pow_succ]
  have h : (2 : ℝ) ^ n * 2 * t - ((k : ℝ) + (2 : ℝ) ^ n) =
      (2 : ℝ) ^ n * (2 * t - 1) - k := by ring
  rw [h]
  ring

theorem dyadicTent_upper_zero (n k : ℕ) (t : ℝ) (ht : t ≤ 1 / 2) :
    dyadicTent (n + 1) (k + 2 ^ n) t = 0 := by
  unfold dyadicTent scaledSchauderTent
  have hp : (0 : ℝ) ≤ 2 ^ n := by positivity
  have harg : (2 : ℝ) ^ (n + 1) * t - (k + 2 ^ n : ℕ) ≤ 0 := by
    push_cast
    rw [pow_succ]
    nlinarith [mul_nonneg hp (show 0 ≤ 1 / 2 - t by linarith), Nat.cast_nonneg (α := ℝ) k]
  rw [schauderTent_eq_zero_left _ harg, mul_zero]

theorem dyadicTent_lower_zero (n k : ℕ) (t : ℝ) (ht : 1 / 2 ≤ t) (hk : k < 2 ^ n) :
    dyadicTent (n + 1) k t = 0 := by
  unfold dyadicTent scaledSchauderTent
  have hp : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hk
  have harg : 1 ≤ (2 : ℝ) ^ (n + 1) * t - k := by
    rw [pow_succ]
    nlinarith [mul_nonneg hp (show 0 ≤ t - 1 / 2 by linarith)]
  rw [schauderTent_eq_zero_right _ harg, mul_zero]

theorem dyadicTent_left_product (n k : ℕ) (s t : ℝ) :
    dyadicTent (n + 1) k s * dyadicTent (n + 1) k t =
      dyadicTent n k (2 * s) * dyadicTent n k (2 * t) / 2 := by
  rw [dyadicTent_left_scale, dyadicTent_left_scale]
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  calc
    _ = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) *
      (dyadicTent n k (2 * s) * dyadicTent n k (2 * t)) := by ring
    _ = _ := by rw [h]; ring

theorem dyadicTent_right_product (n k : ℕ) (s t : ℝ) :
    dyadicTent (n + 1) (k + 2 ^ n) s * dyadicTent (n + 1) (k + 2 ^ n) t =
      dyadicTent n k (2 * s - 1) * dyadicTent n k (2 * t - 1) / 2 := by
  rw [dyadicTent_right_scale, dyadicTent_right_scale]
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  calc
    _ = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) *
      (dyadicTent n k (2 * s - 1) * dyadicTent n k (2 * t - 1)) := by ring
    _ = _ := by rw [h]; ring

noncomputable def dyadicLayerKernel (n : ℕ) (s t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), dyadicTent n k s * dyadicTent n k t

theorem dyadicLayerKernel_left (n : ℕ) (s t : ℝ) (hs : s ≤ 1 / 2) :
    dyadicLayerKernel (n + 1) s t = dyadicLayerKernel n (2 * s) (2 * t) / 2 := by
  unfold dyadicLayerKernel
  rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
  simp only [Nat.add_comm (2 ^ n)]
  simp_rw [dyadicTent_upper_zero n _ s hs, zero_mul, dyadicTent_left_product]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_div]

theorem dyadicLayerKernel_right (n : ℕ) (s t : ℝ) (hs : 1 / 2 ≤ s) :
    dyadicLayerKernel (n + 1) s t = dyadicLayerKernel n (2 * s - 1) (2 * t - 1) / 2 := by
  unfold dyadicLayerKernel
  rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range (2 ^ n),
      dyadicTent (n + 1) k s * dyadicTent (n + 1) k t) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [dyadicTent_lower_zero n k s hs (Finset.mem_range.mp hk), zero_mul]
  rw [hz, zero_add]
  simp only [Nat.add_comm (2 ^ n)]
  simp_rw [dyadicTent_right_product]
  rw [Finset.sum_div]

theorem dyadicLayerKernel_cross (n : ℕ) (s t : ℝ) (hs : s ≤ 1 / 2) (ht : 1 / 2 ≤ t) :
    dyadicLayerKernel (n + 1) s t = 0 := by
  unfold dyadicLayerKernel
  rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range (2 ^ n),
      dyadicTent (n + 1) k s * dyadicTent (n + 1) k t) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [dyadicTent_lower_zero n k t ht (Finset.mem_range.mp hk), mul_zero]
  rw [hz, zero_add]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Nat.add_comm (2 ^ n), dyadicTent_upper_zero n k s hs, zero_mul]

theorem dyadicLayerKernel_symm (n : ℕ) (s t : ℝ) :
    dyadicLayerKernel n s t = dyadicLayerKernel n t s := by
  simp only [dyadicLayerKernel, mul_comm]

theorem dyadicLayerKernel_zero (s t : ℝ) :
    dyadicLayerKernel 0 s t = schauderTent s * schauderTent t := by
  simp [dyadicLayerKernel, dyadicTent, scaledSchauderTent]

end SRWTightness
