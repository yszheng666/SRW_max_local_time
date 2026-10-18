import SRWTightness.SourceUpperDepthInternal

open Filter
open scoped Topology
namespace SRWTightness

/-- A fourth-power error controls the root error with the full cubic denominator. -/
theorem fourth_root_difference_bound (a b B : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (herr : |a ^ 4 - b ^ 4| ≤ B) : |a - b| ≤ B / b ^ 3 := by
  let F : ℝ := a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3
  have hF : b ^ 3 ≤ F := by
    dsimp [F]
    nlinarith [pow_nonneg ha 3, mul_nonneg (sq_nonneg a) hb.le,
      mul_nonneg ha (sq_nonneg b)]
  have hF0 : 0 ≤ F := (by positivity : 0 ≤ b ^ 3).trans hF
  have he : (a - b) * F = a ^ 4 - b ^ 4 := by dsimp [F]; ring
  have hh : |a - b| * b ^ 3 ≤ B := by
    calc
      _ ≤ |a - b| * F := mul_le_mul_of_nonneg_left hF (abs_nonneg _)
      _ = |a ^ 4 - b ^ 4| := by rw [← he, abs_mul, abs_of_nonneg hF0]
      _ ≤ B := herr
  exact (le_div_iff₀ (by positivity : 0 < b ^ 3)).mpr hh

/-- The actual Green fourth root has the source8log(t) expansion with error tending to zero. -/
theorem source_upper_quarter_root_internal :
    Tendsto (fun t : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) -
      8 * Real.log t) atTop (𝓝 0) := by
  let B : ℝ := diskGreenEnergyConstant / (2 / Real.pi) + 2
  have hg : Tendsto (fun t : ℝ ↦ (8 * Real.log t) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 8))
  have hlim : Tendsto (fun t : ℝ ↦ B / (8 * Real.log t) ^ 3) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0)).comp hg).const_mul B
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [source_upper_terminal_depth_internal,
    eventually_gt_atTop (1 : ℝ)] with t hd ht
  have hd0 : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    unfold upperTerminalDepth diskGreen
    exact div_nonneg (killedGreen_nonneg _ _ _) (by positivity)
  have hp : (upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ^ 4 =
      upperTerminalDepth (sourceUpperLogRadius t) := by
    have hh := Real.rpow_mul_natCast hd0 (1 / 4 : ℝ) 4
    norm_num at hh
    exact hh.symm
  have hroot := fourth_root_difference_bound
    (upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) (8 * Real.log t) B
    (Real.rpow_nonneg hd0 _) (mul_pos (by norm_num) (Real.log_pos ht))
    (by rw [hp]; exact hd)
  simpa only [Real.norm_eq_abs] using hroot

end SRWTightness
