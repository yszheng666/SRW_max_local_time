import SRWTightness.CoarseExponentExpansion

open Filter
open scoped Topology

namespace SRWTightness

/-- The first expansion in manuscript (7.26), for the actual floor and Green-function time. -/
theorem source_coarse_exponent_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      |(sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) ^ 2 /
          (2 * (sourceCoarseGeneration t : ℝ)) -
        (2 * t - 2 * sourceLowerTime (sourceLowerRadius t) - 2 * Real.log t)| ≤ C := by
  have hEpos := sourceTotalTimeError_pos
  refine ⟨2 * sourceTotalTimeError + 7, by positivity, ?_⟩
  have hlog : Tendsto (fun t : ℝ ↦ Real.log t ^ 2 / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hl := (tendsto_order.1 hlog).2 1 (by norm_num)
  have hw := (tendsto_order.1 sourceBarrierSlope_weighted_tendsto_zero).2 1
    (by norm_num)
  filter_upwards [source_deficit_large_conditions, source_coarse_terminal_error_uniform,
    eventually_ge_atTop (4 * sourceTotalTimeError ^ 2), hl, hw] with t ht hN hEt hl hw
  obtain ⟨ht, htE, hdsmall, hlogsmall⟩ := ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 < t := by linarith
  have hT := sourceTotalTime_ge_half t ht htE
  have hterr := sourceTotalTime_error t ht
  have hd := sourceLowerTime_ge_one t ht
  have hs := sourceBarrierSlope_bounds t ht htE
  have hl2 : Real.log t ^ 2 ≤ t := by
    have hh := (div_lt_iff₀ ht0).mp hl
    linarith
  have hbound := coarse_exponent_remainder_bound t
    (sourceLowerTime (sourceLowerRadius t)) (sourceTotalTime t) (Real.log t)
    sourceTotalTimeError ht0 hT sourceTotalTimeError_pos.le hterr hl2 hEt
    (by linarith) hs hw.le
  have htime : sourceTotalTime t - sourceLowerTime (sourceLowerRadius t) =
      (sourceCoarseGeneration t : ℝ) := by unfold sourceTotalTime; ring
  have hmain : (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) ^ 2 /
      (2 * (sourceCoarseGeneration t : ℝ)) =
        sourceBarrierSlope t ^ 2 * (sourceCoarseGeneration t : ℝ) / 2 := by
    field_simp [hN.1.ne']
    <;> ring
  change |sourceBarrierSlope t ^ 2 *
    (sourceTotalTime t - sourceLowerTime (sourceLowerRadius t)) / 2 - _| ≤ _ at hbound
  rw [htime] at hbound
  rw [hmain]
  exact hbound

end SRWTightness
