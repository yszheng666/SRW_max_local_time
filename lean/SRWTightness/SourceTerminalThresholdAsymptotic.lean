import SRWTightness.SourceDeficitBand

open Filter
open scoped Topology

namespace SRWTightness

noncomputable def sourceTerminalThresholdError (t : ℝ) : ℝ :=
  (1 / (t * (2 / Real.pi)) + 224 * t / sourceLowerRadius t) +
    4 * sourceTotalTimeError * (sourceLowerTime (sourceLowerRadius t) / t) +
    20 * sourceLowerTimeSmallQuantity t

theorem sourceTerminalThresholdError_tendsto_zero :
    Tendsto sourceTerminalThresholdError atTop (𝓝 0) := by
  have hh := (sourceTerminalThreshold_ideal_error_tendsto_zero.add
    (sourceLowerTime_div_t_tendsto_zero.const_mul (4 * sourceTotalTimeError))).add
      (source_lower_time_small_error.const_mul 20)
  change Tendsto (fun t : ℝ ↦ sourceTerminalThresholdError t) atTop (𝓝 0)
  simpa only [mul_zero, add_zero, sourceTerminalThresholdError] using hh

/-- Explicit uniform error bound in the original square-root deficit band. -/
theorem sourceTerminalThreshold_target_error (t q : ℝ) (ht : sourceScaleThreshold 4 ≤ t)
    (htE : 2 * sourceTotalTimeError ≤ t)
    (hdsmall : 12 * sourceLowerTime (sourceLowerRadius t) ≤ t) (hlog : Real.log t ≤ t / 2)
    (hq : Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q)
    (hq2 : q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) :
    |sourceTerminalThreshold t (sourceTerminalRoot t q) -
      (2 * sourceLowerTime (sourceLowerRadius t) + q)| ≤ sourceTerminalThresholdError t := by
  let d := sourceLowerTime (sourceLowerRadius t)
  let u := sourceTerminalRoot t q
  let y := sourceTerminalHeight t
  have hd : 1 ≤ d := sourceLowerTime_ge_one t ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 < t := by linarith
  have hu := sourceTerminalRoot_bounds t q ht htE hdsmall hlog hq hq2
  have hu0 : 0 < u := ht0.trans_le hu.1
  have hgap := sourceTerminalRoot_gap_bounds t q ht htE hq hq2
  have hbase := sourceTerminalThreshold_uniform_ideal_error t u ht hu.1 hu.2
  have hsq : (y - u) ^ 2 / (2 * u) ≤ 18 * d ^ 2 / t := by
    have hh := mul_self_le_mul_self hgap.1 hgap.2
    have hnum : (y - u) ^ 2 ≤ 36 * d ^ 2 := by nlinarith
    calc
      _ ≤ (36 * d ^ 2) / (2 * u) := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (36 * d ^ 2) / (2 * t) := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (by linarith [hu.1])
      _ = _ := by ring
  have hslope := sourceBarrierSlope_weighted_error t ht htE
  have he : (y ^ 2 - u ^ 2) / (2 * u) - (2 * d + q) =
      (y - u) ^ 2 / (2 * u) + (sourceBarrierSlope t - 2) * d :=
    terminalThreshold_deficit_identity u y (sourceBarrierSlope t) d q hu0
      (sourceTerminalRoot_gap t q ht htE)
  have hrest : |(y ^ 2 - u ^ 2) / (2 * u) - (2 * d + q)| ≤
      18 * d ^ 2 / t +
        (4 * sourceTotalTimeError * (d / t) + 2 * sourceLowerTimeSmallQuantity t) := by
    rw [he]
    have ha := abs_add_le ((y - u) ^ 2 / (2 * u)) ((sourceBarrierSlope t - 2) * d)
    rw [abs_of_nonneg (by positivity : 0 ≤ (y - u) ^ 2 / (2 * u)),
      abs_mul, abs_of_nonneg (show 0 ≤ d by linarith)] at ha
    exact ha.trans (add_le_add hsq hslope)
  have htri := (abs_sub_le (sourceTerminalThreshold t u) ((y ^ 2 - u ^ 2) / (2 * u))
    (2 * d + q)).trans (add_le_add hbase hrest)
  have hlog0 := Real.log_nonneg (show 1 ≤ t by linarith)
  have hminor : d ^ 2 / t ≤ sourceLowerTimeSmallQuantity t := by
    unfold sourceLowerTimeSmallQuantity
    have hh : 0 ≤ d * Real.log t / t := by positivity
    change d ^ 2 / t ≤ d ^ 2 / t + d * Real.log t / t
    linarith
  change |sourceTerminalThreshold t u - (2 * d + q)| ≤ _
  unfold sourceTerminalThresholdError
  change |sourceTerminalThreshold t u - (2 * d + q)| ≤
    (1 / (t * (2 / Real.pi)) + 224 * t / sourceLowerRadius t) +
      4 * sourceTotalTimeError * (d / t) + 20 * sourceLowerTimeSmallQuantity t
  rw [mul_div_assoc 18 (d ^ 2) t] at htri
  linarith

/-- Manuscript (7.19): a single error tending to zero controls every allowed terminal deficit. -/
theorem source_terminal_threshold_asymptotic :
    Tendsto sourceTerminalThresholdError atTop (𝓝 0) ∧
    ∀ᶠ t : ℝ in atTop, ∀ q : ℝ,
      Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
      q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
      |sourceTerminalThreshold t (sourceTerminalRoot t q) -
        (2 * sourceLowerTime (sourceLowerRadius t) + q)| ≤ sourceTerminalThresholdError t := by
  refine ⟨sourceTerminalThresholdError_tendsto_zero, ?_⟩
  filter_upwards [source_deficit_large_conditions] with t ht
  intro q hq hq2
  exact sourceTerminalThreshold_target_error t q ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hq hq2

end SRWTightness
