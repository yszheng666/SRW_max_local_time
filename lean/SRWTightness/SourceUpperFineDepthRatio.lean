import SRWTightness.SourceUpperDepthInternal

open Filter
open scoped Topology
namespace SRWTightness

/-- The actual Green terminal depth grows without bound. -/
theorem source_upper_depth_tendsto_internal :
    Tendsto (fun t : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius t)) atTop atTop := by
  let B : ℝ := diskGreenEnergyConstant / (2 / Real.pi) + 2
  apply tendsto_atTop.2
  intro b
  filter_upwards [source_upper_terminal_depth_internal,
    sourceUpperLogRadius_eventually (b + B)] with t hd ht
  have hh := (abs_le.mp hd).1
  dsimp [B] at ht
  linarith

/-- The logarithm of the integer fine radius divided by actual Green depth tends to one quarter. -/
theorem source_upper_fine_depth_ratio_internal :
    Tendsto (fun t : ℝ ↦ Real.log (upperTerminalFineRadius (sourceUpperLogRadius t)) /
      upperTerminalDepth (sourceUpperLogRadius t)) atTop (𝓝 (1 / 4)) := by
  let B : ℝ := diskGreenEnergyConstant / (2 / Real.pi) + 2
  let C : ℝ := 1 + B / 4
  have hlim : Tendsto (fun t : ℝ ↦ C / upperTerminalDepth (sourceUpperLogRadius t))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0)).comp
        source_upper_depth_tendsto_internal).const_mul C
  obtain ⟨u₀, _, hs⟩ := exponential_floor_scale_input 1 (by norm_num)
  have hz : Tendsto (fun t : ℝ ↦
      Real.log (upperTerminalFineRadius (sourceUpperLogRadius t)) /
        upperTerminalDepth (sourceUpperLogRadius t) - 1 / 4) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hlim
    filter_upwards [source_upper_terminal_depth_internal,
      sourceUpperLogRadius_eventually u₀,
      source_upper_depth_tendsto_internal.eventually (eventually_gt_atTop (0 : ℝ))]
      with t hd hu hd0
    have hr := (hs (sourceUpperLogRadius t) hu).2.2.2.2.2
    have he : Real.log (upperTerminalFineRadius (sourceUpperLogRadius t)) -
        upperTerminalDepth (sourceUpperLogRadius t) / 4 =
        (Real.log (upperTerminalFineRadius (sourceUpperLogRadius t)) -
          sourceUpperLogRadius t / 4) +
        (sourceUpperLogRadius t - upperTerminalDepth (sourceUpperLogRadius t)) / 4 := by ring
    have hb : |Real.log (upperTerminalFineRadius (sourceUpperLogRadius t)) -
        upperTerminalDepth (sourceUpperLogRadius t) / 4| ≤ C := by
      rw [he]
      apply (abs_add_le _ _).trans
      dsimp [C, B]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_sub_comm (sourceUpperLogRadius t) (upperTerminalDepth (sourceUpperLogRadius t))]
      exact add_le_add hr (div_le_div_of_nonneg_right hd (by norm_num))
    have he' : Real.log (upperTerminalFineRadius (sourceUpperLogRadius t)) /
        upperTerminalDepth (sourceUpperLogRadius t) - 1 / 4 =
        (Real.log (upperTerminalFineRadius (sourceUpperLogRadius t)) -
          upperTerminalDepth (sourceUpperLogRadius t) / 4) /
            upperTerminalDepth (sourceUpperLogRadius t) := by
      field_simp [hd0.ne']
    rw [Real.norm_eq_abs, he', abs_div, abs_of_pos hd0]
    exact div_le_div_of_nonneg_right hb hd0.le
  have hh := hz.add_const (1 / 4 : ℝ)
  simpa only [sub_add_cancel, zero_add] using hh

end SRWTightness
