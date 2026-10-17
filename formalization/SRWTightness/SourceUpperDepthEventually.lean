import SRWTightness.SourceUpperDepthError

open Filter
open scoped Topology
namespace SRWTightness

/-- Reuse mathlib's logarithmic power asymptotic for the exact upper scale. -/
theorem sourceUpperLogRadius_div_tendsto :
    Tendsto (fun t : ℝ ↦ sourceUpperLogRadius t / t) atTop (𝓝 0) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero
  have hh := h.const_mul (8 ^ 4 : ℝ)
  convert hh using 1 <;> simp only [sourceUpperLogRadius, id_eq, mul_zero] <;> ring

/-- The natural coarse floor eventually agrees with the positive-depth source regime. -/
theorem source_upper_coarse_range_eventually :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t - sourceUpperLogRadius t - Real.log 32 := by
  have hsmall := sourceUpperLogRadius_div_tendsto.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, eventually_ge_atTop (max 1 (2 * (Real.log 32 + 1)))] with t hs ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans ht)
  have hlarge := (le_max_right _ _).trans ht
  have hD := (div_lt_iff₀ ht0).mp hs
  linarith

/-- Existing Green and elementary scale inputs give the actual bounded total-depth drift. -/
theorem source_upper_total_depth_eventually (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop,
      |sourceUpperTotalDepth t - t| ≤
        diskGreenEnergyConstant / (2 / Real.pi) + Real.log 32 + 4 := by
  obtain ⟨u₀, _, hscale⟩ := hScale 1 (by norm_num)
  filter_upwards [sourceUpperLogRadius_eventually u₀,
    source_upper_coarse_range_eventually] with t hu ht
  obtain ⟨hR, _, _, _, hlog, _⟩ := hscale (sourceUpperLogRadius t) hu
  have hd := source_upper_terminal_depth_error (sourceUpperLogRadius t) hR hlog
  have hh := source_upper_total_depth_error t
    (diskGreenEnergyConstant / (2 / Real.pi) + 2) ht hd
  convert hh using 1 <;> ring

end SRWTightness
