import SRWTightness.SourceUpperBarrierDefinition
import SRWTightness.SourceUpperSlopeError

open Filter
open scoped Topology

namespace SRWTightness

/-- Every source barrier is eventually bounded by four times logarithmic radius. -/
theorem source_upper_barrier_uniform_height (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t → sourceUpperBarrier t s j ≤ 4 * t := by
  obtain ⟨B, hB, hcond⟩ := source_upper_threshold_conditions hScale
  have hlim : Tendsto (fun t : ℝ ↦ (1 + Real.sqrt Real.pi) * (Real.log t / t))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  filter_upwards [hcond, hlim.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (max 2 (2 * (B + 4)))] with t ht hl hlarge
  intro s hs hslog j hj
  have ht2 : 2 ≤ t := (le_max_left _ _).trans hlarge
  have htB : 2 * (B + 4) ≤ t := (le_max_right _ _).trans hlarge
  have hT : 1 ≤ sourceUpperTotalDepth t := by linarith [ht.2.2.2.1]
  have hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    linarith [ht.2.2.2.2.2.2.1]
  have hjT : (j : ℝ) ≤ sourceUpperTotalDepth t := by
    have hj' : (j : ℝ) ≤ sourceUpperCoarseDepth t := by exact_mod_cast hj
    unfold sourceUpperTotalDepth
    linarith
  have hy := source_upper_height_bounds t s ht.1 hs hslog
  have hθ : 0 ≤ sourceUpperSlope t s := div_nonneg (by linarith [hy.1]) (by linarith)
  have hlinear : sourceUpperSlope t s * j ≤ sourceUpperHeight t s := by
    calc
      _ ≤ sourceUpperSlope t s * sourceUpperTotalDepth t :=
        mul_le_mul_of_nonneg_left hjT hθ
      _ = _ := div_mul_cancel₀ _ (by linarith)
  have hc : sourceUpperBarrierCurvature t j ≤ sourceUpperTotalDepth t := by
    unfold sourceUpperBarrierCurvature
    exact (Real.rpow_le_rpow (le_min (Nat.cast_nonneg _) (sub_nonneg.mpr hjT))
      ((min_le_left _ _).trans hjT) (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans
        (Real.rpow_le_self_of_one_le hT (by norm_num))
  have hlog : (1 + Real.sqrt Real.pi) * Real.log t ≤ t / 2 := by
    have hh : (1 + Real.sqrt Real.pi) * Real.log t / t < 1 / 2 := by
      simpa only [mul_div_assoc] using hl
    have := (div_lt_iff₀ ht.1).mp hh
    linarith
  have hThi := (abs_le.mp ht.2.2.2.2.1).2
  unfold sourceUpperBarrier
  nlinarith [hy.2]

/-- Being below the source barrier forces the manuscript generation cap. -/
theorem source_upper_barrier_count_cap (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t → ∀ n : ℕ,
        Real.sqrt (2 * (n : ℝ)) ≤ sourceUpperBarrier t s j → (n : ℝ) ≤ 16 * t ^ 2 := by
  filter_upwards [source_upper_barrier_uniform_height hScale,
    eventually_ge_atTop (0 : ℝ)] with t ht ht0
  intro s hs hslog j hj n hn
  have hh := hn.trans (ht s hs hslog j hj)
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * (n : ℝ) by positivity)
  nlinarith [Real.sqrt_nonneg (2 * (n : ℝ)), sq_nonneg t]

end SRWTightness
