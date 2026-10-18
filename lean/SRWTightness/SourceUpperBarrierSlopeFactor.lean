import SRWTightness.UpperBarrierSlopeFactor
import SRWTightness.SourceUpperThresholdConditions
import SRWTightness.SourceUpperSlopeError

open Filter
open scoped Topology
namespace SRWTightness

/-- The source slope stays in the fixed range needed by the spatial barrier estimate. -/
theorem source_upper_barrier_slope_bounds (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      3 / 2 ≤ sourceUpperSlope t s ∧ sourceUpperSlope t s ≤ 3 := by
  obtain ⟨B, hB, hcond⟩ := source_upper_threshold_conditions hScale
  have hlim : Tendsto (fun t : ℝ ↦ (1 + Real.sqrt Real.pi) * (Real.log t / t))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hl := hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [hcond, hl, eventually_ge_atTop (16 * B)] with t ht hl htB
  intro s hs hslog
  have hlog : (1 + Real.sqrt Real.pi) * Real.log t ≤ t / 8 := by
    have hh : (1 + Real.sqrt Real.pi) * Real.log t / t < 1 / 8 := by
      simpa only [mul_div_assoc] using hl
    have hh' := (div_lt_iff₀ ht.1).mp hh
    linarith
  have herror := source_upper_slope_error t s B ht.1 hs hslog ht.2.2.2.1 ht.2.2.2.2.1
  have he : 2 * ((1 + Real.sqrt Real.pi) * Real.log t + 2 * B) / t ≤ 1 / 2 := by
    apply (div_le_iff₀ ht.1).mpr
    linarith
  have hh := abs_le.mp (herror.trans he)
  constructor <;> linarith

/-- The slope correction loses only the exact quadratic factor in the generation index. -/
theorem source_upper_barrier_slope_factor (hScale : ExponentialFloorScaleInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s →
      ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t →
      Real.exp ((2 - sourceUpperSlope t s ^ 2 / 2) * (j : ℝ)) ≤
        C * ((j : ℝ) + 1) ^ 2 := by
  obtain ⟨B, hB, hcond⟩ := source_upper_threshold_conditions hScale
  refine ⟨4 * Real.exp (4 * B), by positivity, ?_⟩
  filter_upwards [hcond, eventually_ge_atTop (2 : ℝ)] with t ht ht2
  intro s hs j hj
  have hT : 1 ≤ sourceUpperTotalDepth t := by linarith [ht.2.2.2.1]
  have hT0 : 0 < sourceUpperTotalDepth t := by linarith
  have hTB := (abs_le.mp ht.2.2.2.2.1).2
  have hheight : 2 * t - Real.log t ≤ sourceUpperSlope t s * sourceUpperTotalDepth t := by
    unfold sourceUpperSlope
    rw [div_mul_cancel₀ _ hT0.ne']
    unfold sourceUpperHeight
    exact le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) hs)
  have hjT : (j : ℝ) ≤ sourceUpperTotalDepth t := by
    have hj' : (j : ℝ) ≤ (sourceUpperCoarseDepth t : ℝ) := by exact_mod_cast hj
    have hd := ht.2.2.2.2.2.2.1
    unfold sourceUpperTotalDepth
    linarith
  exact upper_barrier_slope_factor t (sourceUpperTotalDepth t) (sourceUpperSlope t s) B j
    ht.1 hT ht.2.2.2.1 hTB hB hheight (Nat.cast_nonneg _) hjT

end SRWTightness
