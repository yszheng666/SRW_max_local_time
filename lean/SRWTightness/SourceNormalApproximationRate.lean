import SRWTightness.SourceTimePowerDecay
import SRWTightness.SourceGreenScaleComparison

open Filter
open scoped Topology

namespace SRWTightness

/-- The dimension factor in the convex-set bound is at most a quadratic polynomial. -/
theorem normal_approximation_dimension_factor (p : ℕ) :
    (42 * (p : ℝ) ^ (1 / 4 : ℝ) + 16) * p * Real.sqrt p ≤ 58 * (p : ℝ) ^ 2 := by
  by_cases hp : p = 0
  · subst p; simp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hr : (p : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt p := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have hs : Real.sqrt (p : ℝ) ≤ p := Real.sqrt_le_self_iff.mpr (Or.inr hp1)
  have hs2 := Real.sq_sqrt hp0
  have h := mul_le_mul_of_nonneg_right hr (show 0 ≤ 42 * (p : ℝ) * Real.sqrt p by positivity)
  have h' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 16 * (p : ℝ) by positivity)
  nlinarith

/-- The explicit convex-set coefficient times the source moment bound is O(d^5/t). -/
theorem normal_approximation_rate_bound (p : ℕ) (C P d t : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hp : (p : ℝ) ≤ P * d) :
    (42 * (p : ℝ) ^ (1 / 4 : ℝ) + 16) *
      (C * p * Real.sqrt p * d ^ 3 / t) ≤ 58 * C * P ^ 2 * d ^ 5 / t := by
  have hdim := normal_approximation_dimension_factor p
  have hp2 : (p : ℝ) ^ 2 ≤ (P * d) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg p) hp 2
  have h1 := mul_le_mul_of_nonneg_right hdim (show 0 ≤ C * d ^ 3 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 58 * C * d ^ 3 by positivity)
  have hn : (42 * (p : ℝ) ^ (1 / 4 : ℝ) + 16) *
      (C * p * Real.sqrt p * d ^ 3) ≤ 58 * C * P ^ 2 * d ^ 5 := by
    nlinarith
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hn ht

/-- The source d^5/t error decays faster than every fixed inverse real power of d. -/
theorem source_normal_error_scaled_tendsto_zero (C a : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun t : ℝ ↦
      sourceLowerTime (sourceLowerRadius t) ^ a *
        (C * sourceLowerTime (sourceLowerRadius t) ^ 5 / t)) atTop (𝓝 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt a
  have hm : Tendsto (fun t : ℝ ↦
      C * (sourceLowerTime (sourceLowerRadius t) ^ (n + 5) / t)) atTop (𝓝 0) := by
    simpa using (sourceLowerTime_pow_div_t_tendsto_zero (n + 5)).const_mul C
  apply squeeze_zero' _ _ hm
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have hd := sourceLowerTime_ge_one t ht
    have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (div_nonneg (by positivity) (by linarith))
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have hd := sourceLowerTime_ge_one t ht
    have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
    have hr : sourceLowerTime (sourceLowerRadius t) ^ a ≤
        sourceLowerTime (sourceLowerRadius t) ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hd hn.le
    have hh := mul_le_mul_of_nonneg_right hr
      (show 0 ≤ C * sourceLowerTime (sourceLowerRadius t) ^ 5 / t by positivity)
    refine hh.trans_eq ?_
    rw [pow_add]
    ring

end SRWTightness
