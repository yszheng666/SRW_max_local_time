import SRWTightness.SourceLowerTimeSmallError

open Filter
open scoped Topology

namespace SRWTightness

/-- Every fixed natural power of the actual source Green-function time is negligible relative to t. -/
theorem sourceLowerTime_pow_div_t_tendsto_zero (n : ℕ) :
    Tendsto (fun t : ℝ ↦ sourceLowerTime (sourceLowerRadius t) ^ n / t) atTop (𝓝 0) := by
  let C : ℝ := 2000 ^ 3 + sourceLowerTimeError
  have hC : 0 < C := by dsimp [C]; linarith [sourceLowerTimeError_pos]
  have hl : Tendsto (fun t : ℝ ↦ Real.log t ^ (3 * n) / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 (3 * n) one_ne_zero
  have hmajor : Tendsto (fun t : ℝ ↦ C ^ n * (Real.log t ^ (3 * n) / t)) atTop (𝓝 0) := by
    simpa using hl.const_mul (C ^ n)
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have hd := (sourceLowerTime_square_upper t ht).1
    have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
    exact div_nonneg (pow_nonneg hd _) (by linarith)
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have hconds := sourceScaleThreshold_conditions t 4 (by norm_num) ht
    have ht0 : 0 < t := by linarith [hconds.1]
    have hlog := sourceScaleThreshold_log_lower 4 t ht
    have hm : 2 ≤ sourceLowerRadius t := by linarith [hconds.2.2.1]
    have hd := (sourceLowerTime_square_upper t ht).1
    have hbound : sourceLowerTime (sourceLowerRadius t) ≤ C * Real.log t ^ 3 := by
      have hh := (abs_le.mp (sourceLowerTime_log_bound (sourceLowerRadius t) hm)).2
      rw [log_sourceLowerRadius] at hh
      have hcube := sourceLowerLogRadius_cube_upper t hlog
      have hlog3 : 1 ≤ Real.log t ^ 3 := one_le_pow₀ hlog
      have he := mul_le_mul_of_nonneg_left hlog3 sourceLowerTimeError_pos.le
      dsimp [C]
      rw [mul_pow] at hcube
      nlinarith
    calc
      _ ≤ (C * Real.log t ^ 3) ^ n / t :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hd hbound n) ht0.le
      _ = _ := by rw [mul_pow, ← pow_mul]; ring

end SRWTightness
