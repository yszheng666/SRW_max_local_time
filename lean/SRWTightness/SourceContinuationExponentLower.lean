import SRWTightness.SourceContinuationRange
import SRWTightness.ContinuationExponentIdentity
import SRWTightness.SourceCoarseExponentExpansion

open Filter
namespace SRWTightness

/-- The continuation exponent retains the source decay in the early generation and initial height. -/
theorem source_continuation_exponent_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in atTop, ∀ (ν : ℕ) (x : ℝ),
      ν ≤ 2 * sourceCoarseLowerLevel t → 0 ≤ x →
      2 * t - 2 * sourceLowerTime (sourceLowerRadius t) - 2 * Real.log t +
        2 * ν - 2 * x - K ≤
          (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - x) ^ 2 /
            (2 * ((sourceCoarseGeneration t : ℝ) - ν)) := by
  obtain ⟨C, hC, hc⟩ := source_coarse_exponent_expansion
  refine ⟨C + 2, by positivity, ?_⟩
  have he := (tendsto_order.1 sourceBarrierSlope_weighted_tendsto_zero).2 1 (by norm_num)
  filter_upwards [hc, he, source_continuation_cutoff_reserve,
    source_continuation_remaining_time, source_deficit_large_conditions,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 * sourceTotalTimeError))]
    with t hc he hcut htime ht hlog
  intro ν x hν hx
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  have hrem : 0 < (sourceCoarseGeneration t : ℝ) - ν := by linarith [htime ν hν]
  have hN : (sourceCoarseGeneration t : ℝ) ≠ 0 := by
    have hν0 := Nat.cast_nonneg (α := ℝ) ν
    linarith
  have hνd : (ν : ℝ) ≤ sourceLowerTime (sourceLowerRadius t) := by
    have hh : (ν : ℝ) ≤ 2 * (sourceCoarseLowerLevel t : ℝ) := by exact_mod_cast hν
    exact hh.trans hcut
  have hT := sourceTotalTime_ge_half t ht.1 ht.2.1
  have hTerr := (abs_le.mp (sourceTotalTime_error t ht.1)).1
  have hθ : sourceBarrierSlope t ≤ 2 := by
    unfold sourceBarrierSlope sourceTerminalHeight
    apply (div_le_iff₀ (show 0 < sourceTotalTime t by linarith)).mpr
    linarith
  have hθν : (2 - sourceBarrierSlope t) * ν ≤ 1 := by
    have hh := (mul_le_mul_of_nonneg_left hνd (abs_nonneg (sourceBarrierSlope t - 2))).trans he.le
    rw [abs_of_nonpos (by linarith : sourceBarrierSlope t - 2 ≤ 0)] at hh
    linarith
  have hsq : 2 * (ν : ℝ) - 2 ≤ sourceBarrierSlope t ^ 2 * ν / 2 := by
    nlinarith [mul_nonneg (sq_nonneg (sourceBarrierSlope t - 2)) (Nat.cast_nonneg (α := ℝ) ν)]
  have hxθ := mul_le_mul_of_nonneg_right hθ hx
  have hmain : (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) ^ 2 /
      (2 * (sourceCoarseGeneration t : ℝ)) =
      sourceBarrierSlope t ^ 2 * (sourceCoarseGeneration t : ℝ) / 2 := by
    field_simp
    <;> ring
  rw [hmain] at hc
  have hl := continuation_exponent_lower (sourceBarrierSlope t)
    (sourceCoarseGeneration t : ℝ) (ν : ℝ) x hrem
  linarith [(abs_le.mp hc).1]

end SRWTightness
