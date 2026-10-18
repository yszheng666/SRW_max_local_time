import SRWTightness.SourceCoarseTerminalExponent

open Filter
open scoped Topology

namespace SRWTightness

/-- Uniform error bound for combining the coarse and terminal exponential factors. -/
noncomputable def sourceCoarseTerminalError (t : ℝ) : ℝ :=
  2 * (|sourceBarrierSlope t - 2| * sourceLowerTime (sourceLowerRadius t)) +
    8 * (sourceLowerTime (sourceLowerRadius t) / t)

theorem source_coarse_terminal_error_tendsto_zero :
    Tendsto sourceCoarseTerminalError atTop (𝓝 0) := by
  have hh := (sourceBarrierSlope_weighted_tendsto_zero.const_mul 2).add
    (sourceLowerTime_div_t_tendsto_zero.const_mul 8)
  simp only [mul_zero, add_zero] at hh
  exact hh

/-- Actual source generations control the residual exponent uniformly on the deficit band. -/
theorem source_coarse_terminal_error_uniform :
    ∀ᶠ t : ℝ in atTop, 0 < (sourceCoarseGeneration t : ℝ) ∧
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        |(sourceBarrierSlope t - 2) * q -
          q ^ 2 / (2 * (sourceCoarseGeneration t : ℝ))| ≤ sourceCoarseTerminalError t := by
  filter_upwards [source_deficit_large_conditions] with t ht
  obtain ⟨ht, htE, hdsmall, hlog⟩ := ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 < t := by linarith
  have hd := sourceLowerTime_ge_one t ht
  have hT := sourceTotalTime_ge_half t ht htE
  have hN : t / 4 ≤ (sourceCoarseGeneration t : ℝ) := by
    unfold sourceTotalTime at hT
    linarith
  have hN0 : 0 < (sourceCoarseGeneration t : ℝ) := by linarith
  refine ⟨hN0, ?_⟩
  intro q hql hqu
  have hq0 : 0 ≤ q := (Real.sqrt_nonneg _).trans hql
  have hh := coarse_terminal_exponent_error (sourceBarrierSlope t) q
    (sourceLowerTime (sourceLowerRadius t)) (sourceCoarseGeneration t : ℝ)
    hN0 hd hq0 hqu
  have hdiv : sourceLowerTime (sourceLowerRadius t) /
      (sourceCoarseGeneration t : ℝ) ≤
      sourceLowerTime (sourceLowerRadius t) / (t / 4) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) hN
  unfold sourceCoarseTerminalError
  calc
    _ ≤ 2 * |sourceBarrierSlope t - 2| * sourceLowerTime (sourceLowerRadius t) +
        2 * sourceLowerTime (sourceLowerRadius t) /
          (sourceCoarseGeneration t : ℝ) := hh
    _ ≤ 2 * |sourceBarrierSlope t - 2| * sourceLowerTime (sourceLowerRadius t) +
        2 * (sourceLowerTime (sourceLowerRadius t) / (t / 4)) := by
      have hhdiv := mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ) ≤ 2 by norm_num)
      rw [← mul_div_assoc] at hhdiv
      exact add_le_add le_rfl hhdiv
    _ = _ := by ring

end SRWTightness
