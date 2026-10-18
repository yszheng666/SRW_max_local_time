import SRWTightness.SourceUpperBlockForest
import SRWTightness.SourceUpperDepthEventually

open Filter

namespace SRWTightness

/-- Actual selected roots leave a branching depth between three quarters of t and t. -/
theorem source_upper_branching_depth_bounds :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      sourceUpperBlockRoot t b < sourceUpperCoarseDepth t ∧
      3 * t / 4 ≤ (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) ∧
      (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) ≤ t := by
  filter_upwards [source_upper_block_root_conditions, source_upper_coarse_range_eventually,
    sourceUpperLogRadius_div_tendsto.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    eventually_ge_atTop (max 1 (8 * (Real.log 32 + 3)))] with t hk hc hD hl ht
  intro b hb
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have htC := (le_max_right _ _).trans ht
  have hD' := (div_lt_iff₀ ht0).mp hD
  have hl' := (div_lt_iff₀ ht0).mp hl
  have hN := source_upper_coarse_depth_error t hc
  have hkb := (hk b hb).2.1
  have hgap : 3 * t / 4 ≤ (sourceUpperCoarseDepth t : ℝ) - sourceUpperBlockRoot t b := by
    linarith [hN.1]
  have hlt : sourceUpperBlockRoot t b < sourceUpperCoarseDepth t := by
    have : (sourceUpperBlockRoot t b : ℝ) < sourceUpperCoarseDepth t := by linarith
    exact_mod_cast this
  refine ⟨hlt, ?_, ?_⟩
  · simpa only [Nat.cast_sub hlt.le] using hgap
  · rw [Nat.cast_sub hlt.le]
    have hD0 : 0 ≤ sourceUpperLogRadius t := by unfold sourceUpperLogRadius; positivity
    have hlog : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
    have hkn : (0 : ℝ) ≤ sourceUpperBlockRoot t b := Nat.cast_nonneg _
    linarith [hN.2]

/-- Actual finite-record depth is the remaining coarse branching depth. -/
theorem sourceUpperBlockForestDepth_eq_remaining (t : ℝ) (b : Site) :
    sourceUpperBlockForestDepth t b = sourceUpperCoarseDepth t - sourceUpperBlockRoot t b := by
  unfold sourceUpperBlockForestDepth sourceUpperCoarseDepth
  omega

/-- The root cap places the initial square-root population in the source branching range. -/
theorem source_upper_branching_initial_range :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t, ∀ J : ℕ,
      (J : ℝ) ≤ t ^ 2 → Real.sqrt (2 * (J : ℝ)) ≤
        4 * (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) := by
  filter_upwards [source_upper_branching_depth_bounds, eventually_ge_atTop (0 : ℝ)]
    with t ht ht0
  intro b hb J hJ
  have hL := (ht b hb).2.1
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * (J : ℝ) by positivity)
  have hroot := Real.sqrt_nonneg (2 * (J : ℝ))
  have hh : Real.sqrt (2 * (J : ℝ)) ≤ 2 * t := by nlinarith
  linarith

end SRWTightness
