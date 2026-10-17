import SRWTightness.SourceUpperMarkRadius

open Filter
namespace SRWTightness

/-- A bounded logarithmic depth error controls every diagonal in the actual killing disk. -/
theorem disk_diagonal_log_depth_bound (R d B : ℝ) (hR : 1 ≤ R) (hd : 1 ≤ d)
    (hB : 0 ≤ B) (herr : |d - Real.log R| ≤ B) (z : Site) (hz : z ∈ disk R) :
    diskGreen R z z ≤
      ((2 / Real.pi) + (2 / Real.pi) * B + diskGreenEnergyConstant +
        (2 / Real.pi) * Real.log 2) * d := by
  let g : ℝ := 2 / Real.pi
  have hg : 0 < g := by dsimp [g]; positivity
  have hE := diskGreenEnergyConstant_pos
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have he := (abs_le.mp herr).1
  have hl : Real.log R ≤ d + B := by linarith
  have hm := mul_le_mul_of_nonneg_left hl hg.le
  have hu := diskGreen_diagonal_upper R hR z hz
  change diskGreen R z z ≤ g * Real.log R + (diskGreenEnergyConstant + g * Real.log 2) at hu
  have hc := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ g * B + diskGreenEnergyConstant + g * Real.log 2 by positivity)
  change diskGreen R z z ≤ (g + g * B + diskGreenEnergyConstant + g * Real.log 2) * d
  nlinarith

/-- The padded source killing disk has diagonal variance O(d) in the original reference depth. -/
theorem source_upper_padded_diagonal_variance (hScale : ExponentialFloorScaleInput) :
    ∃ V : ℝ, 0 < V ∧ ∀ᶠ t : ℝ in atTop,
      ∀ z ∈ diskFinset (sourceUpperMarkRadius t),
      killedGreen (diskFinset (sourceUpperMarkRadius t)) z z ≤
        V * upperTerminalDepth (sourceUpperLogRadius t) := by
  let B := diskGreenEnergyConstant / (2 / Real.pi) + Real.log 16
  have hB : 0 ≤ B := by
    have hE := diskGreenEnergyConstant_pos
    have hl : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [B]
    positivity
  let V := (2 / Real.pi) + (2 / Real.pi) * B + diskGreenEnergyConstant +
    (2 / Real.pi) * Real.log 2
  have hV : 0 < V := by
    have hE := diskGreenEnergyConstant_pos
    have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [V]
    positivity
  obtain ⟨B₀, _, ht⟩ := source_upper_threshold_conditions hScale
  refine ⟨V, hV, ?_⟩
  filter_upwards [ht] with t ht
  obtain ⟨_, _, hsize, _, _, _, hd, _⟩ := ht
  obtain ⟨hR, hlo, _⟩ := source_upper_mark_radius_bounds t hsize
  intro z hz
  exact disk_diagonal_log_depth_bound _ _ B (by linarith) hd hB
    (source_upper_mark_radius_depth_error t hsize) z
    (by simpa only [mem_diskFinset] using hz)

end SRWTightness
