import SRWTightness.SourceBarrierSlopeError

open Filter
open scoped Topology

namespace SRWTightness

noncomputable def sourceTerminalRoot (t q : ℝ) : ℝ :=
  sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - q

theorem sourceTerminalRoot_gap (t q : ℝ) (ht : sourceScaleThreshold 4 ≤ t)
    (htE : 2 * sourceTotalTimeError ≤ t) :
    sourceTerminalHeight t - sourceTerminalRoot t q =
      sourceBarrierSlope t * sourceLowerTime (sourceLowerRadius t) + q := by
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hT := sourceTotalTime_ge_half t ht htE
  have hT0 : sourceTotalTime t ≠ 0 := by linarith
  have hh : sourceBarrierSlope t * sourceTotalTime t = sourceTerminalHeight t :=
    div_mul_cancel₀ _ hT0
  unfold sourceTotalTime at hh
  unfold sourceTerminalRoot
  nlinarith

/-- All deficits in the prescribed square-root band have a nonnegative gap at most six d. -/
theorem sourceTerminalRoot_gap_bounds (t q : ℝ) (ht : sourceScaleThreshold 4 ≤ t)
    (htE : 2 * sourceTotalTimeError ≤ t)
    (hq : Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q)
    (hq2 : q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) :
    0 ≤ sourceTerminalHeight t - sourceTerminalRoot t q ∧
      sourceTerminalHeight t - sourceTerminalRoot t q ≤ 6 * sourceLowerTime (sourceLowerRadius t) := by
  have hd := sourceLowerTime_ge_one t ht
  have hs := Real.sqrt_le_self_iff.mpr (Or.inr hd)
  have hq0 : 0 ≤ q := (Real.sqrt_nonneg _).trans hq
  have hb := sourceBarrierSlope_bounds t ht htE
  rw [sourceTerminalRoot_gap t q ht htE]
  constructor
  · exact add_nonneg (mul_nonneg hb.1 (by linarith)) hq0
  · have hh := mul_le_mul_of_nonneg_right hb.2 (show 0 ≤ sourceLowerTime (sourceLowerRadius t) by linarith)
    linarith

/-- The actual terminal root lies in the uniform-threshold range under explicit large-time conditions. -/
theorem sourceTerminalRoot_bounds (t q : ℝ) (ht : sourceScaleThreshold 4 ≤ t)
    (htE : 2 * sourceTotalTimeError ≤ t)
    (hd : 12 * sourceLowerTime (sourceLowerRadius t) ≤ t) (hl : Real.log t ≤ t / 2)
    (hq : Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q)
    (hq2 : q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) :
    t ≤ sourceTerminalRoot t q ∧ sourceTerminalRoot t q ≤ 2 * t := by
  have hg := sourceTerminalRoot_gap_bounds t q ht htE hq hq2
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hlog := Real.log_nonneg (show 1 ≤ t by linarith)
  unfold sourceTerminalHeight at hg
  constructor <;> linarith

/-- The explicit large-time conditions hold uniformly, before choosing the deficit. -/
theorem source_deficit_large_conditions :
    ∀ᶠ t : ℝ in atTop, sourceScaleThreshold 4 ≤ t ∧ 2 * sourceTotalTimeError ≤ t ∧
      12 * sourceLowerTime (sourceLowerRadius t) ≤ t ∧ Real.log t ≤ t / 2 := by
  have hd := (tendsto_order.1 sourceLowerTime_div_t_tendsto_zero).2 (1 / 12 : ℝ) (by norm_num)
  have hlog : Tendsto (fun t : ℝ ↦ Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hl := (tendsto_order.1 hlog).2 (1 / 2 : ℝ) (by norm_num)
  filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4),
    eventually_ge_atTop (2 * sourceTotalTimeError), hd, hl] with t ht htE hd hl
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 < t := by linarith
  have hd' := (div_lt_iff₀ ht0).mp hd
  have hl' := (div_lt_iff₀ ht0).mp hl
  exact ⟨ht, htE, by linarith, by linarith⟩

end SRWTightness
