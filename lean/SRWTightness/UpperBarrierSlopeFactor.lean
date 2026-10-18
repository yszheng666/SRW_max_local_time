import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Logarithmic concavity preserves the degree-two spatial factor at every intermediate depth. -/
theorem upper_barrier_scaled_log_le_log_succ (T j : ℝ)
    (hT : 1 ≤ T) (hj : 0 ≤ j) (hjT : j ≤ T) :
    (j / T) * Real.log T ≤ Real.log (j + 1) := by
  have hT0 : 0 < T := by linarith
  have ha : 0 ≤ j / T := div_nonneg hj hT0.le
  have ha1 : j / T ≤ 1 := (div_le_one hT0).mpr hjT
  have hconc : (j / T) * Real.log (T + 1) + (1 - j / T) * Real.log 1 ≤
      Real.log ((j / T) * (T + 1) + (1 - j / T) * 1) :=
    strictConcaveOn_log_Ioi.concaveOn.2
      (show T + 1 ∈ Set.Ioi (0 : ℝ) by change 0 < T + 1; linarith)
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) ha (by linarith) (by ring)
  have hpoint : (j / T) * (T + 1) + (1 - j / T) * 1 = j + 1 := by
    field_simp
    ring
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hconc
  rw [hpoint] at hconc
  exact (mul_le_mul_of_nonneg_left
    (Real.log_le_log hT0 (by linarith : T ≤ T + 1)) ha).trans hconc

/-- Bounded total-depth drift yields exactly the source's quadratic spatial slope loss. -/
theorem upper_barrier_slope_factor (t T θ B j : ℝ)
    (ht : 0 < t) (hT : 1 ≤ T) (hhalf : t / 2 ≤ T) (hTB : T - t ≤ B)
    (hB : 0 ≤ B) (hheight : 2 * t - Real.log t ≤ θ * T)
    (hj : 0 ≤ j) (hjT : j ≤ T) :
    Real.exp ((2 - θ ^ 2 / 2) * j) ≤
      4 * Real.exp (4 * B) * (j + 1) ^ 2 := by
  have hT0 : 0 < T := by linarith
  have ha : 0 ≤ j / T := div_nonneg hj hT0.le
  have ha1 : j / T ≤ 1 := (div_le_one hT0).mpr hjT
  have hquad : 2 - θ ^ 2 / 2 ≤ 2 * (2 - θ) := by nlinarith [sq_nonneg (θ - 2)]
  have hlinear : 2 * (2 - θ) ≤ (4 * B + 2 * Real.log t) / T := by
    apply (le_div_iff₀ hT0).mpr
    nlinarith
  have hcost := mul_le_mul_of_nonneg_right (hquad.trans hlinear) hj
  rw [show (4 * B + 2 * Real.log t) / T * j =
    4 * B * (j / T) + 2 * (j / T) * Real.log t by ring] at hcost
  have hlog : Real.log t ≤ Real.log T + Real.log 2 := by
    calc
      _ ≤ Real.log (2 * T) := Real.log_le_log ht (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT0.ne']; ring
  have hweighted := mul_le_mul_of_nonneg_left hlog ha
  have hjensen := upper_barrier_scaled_log_le_log_succ T j hT hj hjT
  have hBcost := mul_le_mul_of_nonneg_left ha1 (show 0 ≤ 4 * B by positivity)
  have hlogtwo := mul_le_mul_of_nonneg_right ha1
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have hexponent : (2 - θ ^ 2 / 2) * j ≤
      4 * B + 2 * Real.log 2 + 2 * Real.log (j + 1) := by
    nlinarith
  have hlogexp (x : ℝ) (hx : 0 < x) : Real.exp (2 * Real.log x) = x ^ 2 := by
    rw [show 2 * Real.log x = Real.log x + Real.log x by ring,
      Real.exp_add, Real.exp_log hx]
    ring
  calc
    _ ≤ Real.exp (4 * B + 2 * Real.log 2 + 2 * Real.log (j + 1)) :=
      Real.exp_le_exp.mpr hexponent
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, hlogexp 2 (by norm_num),
        hlogexp (j + 1) (by linarith)]
      ring

end SRWTightness
