import SRWTightness.SourceUpperThresholdConditions

open Filter
namespace SRWTightness

/-- Every disk Green diagonal is bounded by a fixed multiple of its reference depth. -/
theorem disk_diagonal_reference_depth_bound (R : ℝ) (hR : 2 ≤ R)
    (hd : 1 ≤ diskGreen R 0 0 / (2 / Real.pi)) (z : Site) (hz : z ∈ disk R) :
    diskGreen R z z ≤
      ((2 / Real.pi) + 2 * diskGreenEnergyConstant + (2 / Real.pi) * Real.log 2) *
        (diskGreen R 0 0 / (2 / Real.pi)) := by
  let g : ℝ := 2 / Real.pi
  have hg : 0 < g := by dsimp [g]; positivity
  change 1 ≤ diskGreen R 0 0 / g at hd
  have hE := diskGreenEnergyConstant_pos
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have ho := (abs_le.mp (diskGreen_origin_log_bound R hR)).1
  have hz' := diskGreen_diagonal_upper R (by linarith) z hz
  have he : g * (diskGreen R 0 0 / g) = diskGreen R 0 0 :=
    mul_div_cancel₀ _ hg.ne'
  have hm := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 2 * diskGreenEnergyConstant + g * Real.log 2 by positivity)
  change diskGreen R z z ≤
    (g + 2 * diskGreenEnergyConstant + g * Real.log 2) * (diskGreen R 0 0 / g)
  change -diskGreenEnergyConstant ≤ diskGreen R 0 0 - g * Real.log R at ho
  change diskGreen R z z ≤ g * Real.log R + (diskGreenEnergyConstant + g * Real.log 2) at hz'
  nlinarith

/-- A uniform positive variance multiplier works on the actual upper terminal disk. -/
theorem source_upper_diagonal_variance (hScale : ExponentialFloorScaleInput) :
    ∃ V : ℝ, 0 < V ∧ ∀ᶠ t : ℝ in atTop,
      ∀ z ∈ diskFinset (upperTerminalRadius (sourceUpperLogRadius t)),
      killedGreen (diskFinset (upperTerminalRadius (sourceUpperLogRadius t))) z z ≤
        V * upperTerminalDepth (sourceUpperLogRadius t) := by
  let V := (2 / Real.pi) + 2 * diskGreenEnergyConstant + (2 / Real.pi) * Real.log 2
  have hV : 0 < V := by
    have hE := diskGreenEnergyConstant_pos
    have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [V]
    positivity
  refine ⟨V, hV, ?_⟩
  obtain ⟨u₀, _, hs⟩ := source_upper_terminal_scale_conditions hScale 1 1
    (by norm_num) (by norm_num)
  filter_upwards [sourceUpperLogRadius_eventually u₀] with t ht
  intro z hz
  have hh := hs (sourceUpperLogRadius t) ht
  exact disk_diagonal_reference_depth_bound _ hh.1 hh.2.2.2.1 z
    (by simpa only [mem_diskFinset] using hz)

end SRWTightness
