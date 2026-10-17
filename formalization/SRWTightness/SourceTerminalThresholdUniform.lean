import SRWTightness.SourceTerminalThreshold

open Filter
open scoped Topology

namespace SRWTightness

theorem sourceLowerRadius_ge_seventh_power (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t) :
    t ^ 7 ≤ sourceLowerRadius t := by
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hh := Real.exp_le_exp.mpr
    (sourceLowerLogRadius_ge_seven_log t (sourceScaleThreshold_log_lower 4 t ht))
  have he : Real.exp (7 * Real.log t) = t ^ 7 := by
    rw [show (7 : ℝ) = (7 : ℕ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (by linarith : 0 < t)]
  rw [he] at hh
  exact hh

theorem source_time_div_lowerRadius_tendsto_zero :
    Tendsto (fun t : ℝ ↦ t / sourceLowerRadius t) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ ↦ 1 / t ^ 6) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0))
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
    exact div_nonneg (by linarith) (sourceLowerRadius_pos t).le
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
    have ht0 : 0 < t := by linarith
    have hh := div_le_div_of_nonneg_left ht0.le (by positivity : 0 < t ^ 7)
      (sourceLowerRadius_ge_seventh_power t ht)
    exact hh.trans_eq (by field_simp)

/-- Uniform control on the entire terminal range t <= u <= 2t. -/
theorem sourceTerminalThreshold_uniform_ideal_error (t u : ℝ)
    (ht : sourceScaleThreshold 4 ≤ t) (hu : t ≤ u) (hu2 : u ≤ 2 * t) :
    |sourceTerminalThreshold t u - (sourceTerminalHeight t ^ 2 - u ^ 2) / (2 * u)| ≤
      1 / (t * (2 / Real.pi)) + 224 * t / sourceLowerRadius t := by
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := ht0.trans_le hu
  have hm0 := sourceLowerRadius_pos t
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hy0 : 0 ≤ sourceTerminalHeight t := by
    have hh := Real.log_le_sub_one_of_pos ht0
    unfold sourceTerminalHeight
    linarith
  have hy2 : sourceTerminalHeight t ≤ 2 * t := by
    have hh := Real.log_nonneg (show 1 ≤ t by linarith)
    unfold sourceTerminalHeight
    linarith
  have hysq := mul_self_le_mul_self hy0 hy2
  have husq := mul_self_le_mul_self hu0.le hu2
  have hsum : sourceTerminalHeight t ^ 2 + u ^ 2 ≤ 8 * t ^ 2 := by
    nlinarith
  apply (sourceTerminalThreshold_ideal_error t u ht hu0).trans
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right hu hg.le)
  · have hnum := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 28)
    have hden := mul_le_mul_of_nonneg_right hu (sourceLowerRadius_pos t).le
    calc
      _ ≤ 28 * (8 * t ^ 2) / (u * sourceLowerRadius t) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 28 * (8 * t ^ 2) / (t * sourceLowerRadius t) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by field_simp; ring

/-- The uniform rounding and intensity error vanishes, independently of the terminal count. -/
theorem sourceTerminalThreshold_ideal_error_tendsto_zero :
    Tendsto (fun t : ℝ ↦ 1 / (t * (2 / Real.pi)) +
      224 * t / sourceLowerRadius t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ ↦ 1 / (t * (2 / Real.pi))) atTop (𝓝 0) := by
    have hh := tendsto_inv_atTop_zero.div_const (2 / Real.pi : ℝ)
    simpa only [one_div, mul_inv_rev, div_eq_mul_inv, mul_comm, zero_mul, one_mul] using hh
  have h2 := source_time_div_lowerRadius_tendsto_zero.const_mul 224
  have hh := h1.add h2
  simpa only [mul_zero, add_zero, mul_div_assoc] using hh

end SRWTightness
