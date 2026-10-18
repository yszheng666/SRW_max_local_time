import SRWTightness.StretchedExponentialSummable

open Filter

namespace SRWTightness

/-- Any fixed polynomial factor is summable against a positive stretched exponential. -/
theorem polynomial_stretched_exponential_summable (k : ℕ) (c γ : ℝ)
    (hc : 0 < c) (hγ : 0 < γ) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ k * Real.exp (-c * (n : ℝ) ^ γ)) := by
  have hs := stretched_exponential_summable (c / 2) γ (by positivity) hγ
  apply hs.of_norm_bounded_eventually_nat
  have hh := tendsto_natCast_atTop_atTop.eventually
    (affine_log_eventually_le_rpow (k : ℝ) ((k : ℝ) * Real.log 2)
      (c / 2) γ (by positivity) hγ)
  filter_upwards [hh, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1' : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log (n : ℝ) + Real.log 2 := by
    have h := Real.log_le_log (by positivity : 0 < (n : ℝ) + 1)
      (show (n : ℝ) + 1 ≤ (n : ℝ) * 2 by linarith)
    simpa only [Real.log_mul hnpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hcost : (k : ℝ) * Real.log ((n : ℝ) + 1) ≤ c / 2 * (n : ℝ) ^ γ := by
    have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have he : ((n : ℝ) + 1) ^ k = Real.exp ((k : ℝ) * Real.log ((n : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), he, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end SRWTightness
