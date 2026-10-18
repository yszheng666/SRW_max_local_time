import SRWTightness.SourceUpperThresholdConditions
import SRWTightness.SourceUpperBarrierHeightBound

open Filter
open scoped Topology
namespace SRWTightness

/-- The three deterministic error scales displayed in source (4.10). -/
noncomputable def sourceUpperThresholdErrorScale (t : ℝ) : ℝ :=
  1 / t + t * upperTerminalFineRadius (sourceUpperLogRadius t) / sourceUpperRadius t +
    upperTerminalDepth (sourceUpperLogRadius t) * Real.log t / t

theorem source_upper_threshold_error_scale_limit (hScale : ExponentialFloorScaleInput) :
    Tendsto sourceUpperThresholdErrorScale atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ ↦ 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0))
  have hd := source_upper_depth_log_power_limit hScale 1
  change Tendsto (fun t : ℝ ↦ 1 / t +
    t * upperTerminalFineRadius (sourceUpperLogRadius t) / sourceUpperRadius t +
    upperTerminalDepth (sourceUpperLogRadius t) * Real.log t / t) atTop (𝓝 0)
  simpa only [pow_one, add_zero] using (hi.add source_upper_fine_ratio_limit).add hd

/-- Source (4.10), with a single uniform constant and a vanishing explicit error scale. -/
theorem source_upper_manuscript_threshold (hScale : ExponentialFloorScaleInput) :
    ∃ C : ℝ, 0 < C ∧ Tendsto sourceUpperThresholdErrorScale atTop (𝓝 0) ∧
      ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ u : ℝ,
      t - 1 ≤ u → u ≤ sourceUpperTarget t s + (4 + s) +
        upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) →
      ∃ ε : ℝ,
        Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ) / (2 / Real.pi)) -
          Real.sqrt (sourceUpperIntensity t / (2 / Real.pi)) * u =
          2 * upperTerminalDepth (sourceUpperLogRadius t) + (sourceUpperTarget t s - u) + ε ∧
        |ε| ≤ C * sourceUpperThresholdErrorScale t := by
  obtain ⟨B, hB, hc⟩ := source_upper_threshold_conditions hScale
  let U := 8 + Real.sqrt Real.pi
  let A := 2 / (2 / Real.pi)
  let S := 2 * (1 + Real.sqrt Real.pi + 2 * B)
  let M := 56 * U
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨A + S + M, by positivity, source_upper_threshold_error_scale_limit hScale, ?_⟩
  filter_upwards [hc, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  obtain ⟨ht0, hlog, hsize, hT, hBt, hr, hd, hdt⟩ := ht
  intro s hs hslog u hu hbar
  have hu0 : 0 ≤ u := by linarith
  have hT0 : 0 < sourceUpperTotalDepth t := by linarith
  have hub : |u| ≤ U * t := source_upper_barrier_height_bound t s u ht1 hs hslog hu0
    hT0 hd hdt hbar
  obtain ⟨ε, heq, he⟩ := source_upper_uniform_threshold_error t s u B U ht0 hlog hs hslog
    hsize hT hBt hU hub hr (by linarith)
  refine ⟨ε, heq, he.trans ?_⟩
  have hz1 : 0 ≤ 1 / t := by positivity
  have hz2 : 0 ≤ t * upperTerminalFineRadius (sourceUpperLogRadius t) /
      sourceUpperRadius t := by unfold sourceUpperRadius; positivity
  have hz3 : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) * Real.log t / t := by
    positivity
  have h1 := mul_le_mul_of_nonneg_right (show A ≤ A + S + M by linarith) hz1
  have h2 := mul_le_mul_of_nonneg_right (show M ≤ A + S + M by linarith) hz2
  have h3 := mul_le_mul_of_nonneg_right (show S ≤ A + S + M by linarith) hz3
  change A / t + S * (upperTerminalDepth (sourceUpperLogRadius t) * Real.log t / t) +
    M * (t * upperTerminalFineRadius (sourceUpperLogRadius t) / sourceUpperRadius t) ≤ _
  unfold sourceUpperThresholdErrorScale
  have hh := add_le_add (add_le_add h1 h3) h2
  convert hh using 1 <;> (congr 1 <;> ring)

end SRWTightness
