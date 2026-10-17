import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace SRWTightness

/-- The standard dyadic chaining thresholds have an exact summable total. -/
theorem dyadic_chaining_weight_hasSum (u : ℝ) :
    HasSum (fun n : ℕ ↦ (u + n + 1) / (2 : ℝ) ^ n) (2 * u + 4) := by
  have hg : HasSum (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) 2 := by
    convert hasSum_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num) using 1 <;>
      norm_num <;> rfl
  have hn : HasSum (fun n : ℕ ↦ (n : ℝ) * (1 / 2 : ℝ) ^ n) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one
      (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num) using 1 <;> norm_num <;> rfl
  convert (hg.mul_left (u + 1)).add hn using 1 <;> try rfl
  · funext n
    simp only [div_eq_mul_inv, one_div, inv_pow, Pi.add_apply]
    ring <;> norm_num
  · ring

/-- Every finite initial sum of nonnegative chaining thresholds is bounded by that total. -/
theorem dyadic_chaining_weight_sum_le (u : ℝ) (hu : 0 ≤ u) (N : ℕ) :
    (∑ n ∈ Finset.range N, (u + n + 1) / (2 : ℝ) ^ n) ≤ 2 * u + 4 := by
  have hh := (dyadic_chaining_weight_hasSum u).summable.sum_le_tsum
    (Finset.range N) (fun n _ ↦ by positivity)
  rwa [(dyadic_chaining_weight_hasSum u).tsum_eq] at hh

/-- A finite chain crossing its total threshold has a single increment crossing its threshold. -/
theorem finite_chain_crossing_increment (f w : ℕ → ℝ) (N : ℕ) (U : ℝ)
    (h0 : f 0 = 0) (hU : U ≤ |f (N + 1)|)
    (hs : (∑ n ∈ Finset.range (N + 1), w n) ≤ U) :
    ∃ n < N + 1, w n ≤ |f (n + 1) - f n| := by
  by_contra h
  have hlt : ∀ n ∈ Finset.range (N + 1), |f (n + 1) - f n| < w n := by
    intro n hn
    exact lt_of_not_ge (fun hh ↦ h ⟨n, Finset.mem_range.mp hn, hh⟩)
  have hsum : (∑ n ∈ Finset.range (N + 1), |f (n + 1) - f n|) <
      ∑ n ∈ Finset.range (N + 1), w n := by
    exact Finset.sum_lt_sum (fun n hn ↦ (hlt n hn).le)
      ⟨0, by simp, hlt 0 (by simp)⟩
  have habs := Finset.abs_sum_le_sum_abs (s := Finset.range (N + 1))
    (f := fun n ↦ f (n + 1) - f n)
  rw [Finset.sum_range_sub, h0, sub_zero] at habs
  linarith

/-- Quadratic Gaussian decay dominates the dimension-two dyadic edge count. -/
theorem dyadic_gaussian_edge_weight_summable :
    Summable (fun n : ℕ ↦ (16 : ℝ) ^ n * Real.exp (-((n : ℝ) + 1) ^ 2 / 2)) := by
  apply (Real.summable_exp_neg_nat.mul_left
    (Real.exp ((Real.log 16 + 1) ^ 2))).of_nonneg_of_le (fun n ↦ by positivity)
  intro n
  have he : (16 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 16) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  rw [he, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ((n : ℝ) - (Real.log 16 + 1)),
    sq_nonneg (Real.log 16 + 1), Nat.cast_nonneg (α := ℝ) n]

end SRWTightness
