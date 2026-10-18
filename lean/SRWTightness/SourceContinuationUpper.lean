import SRWTightness.SourceContinuationRange
import SRWTightness.SourceContinuationWindow

open Filter MeasureTheory
namespace SRWTightness

/-- Uniform application of the external GW upper bound throughout the source early range. -/
theorem source_continuation_upper (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (q : ℝ) (ν L k : ℕ),
      ν ≤ 2 * sourceCoarseLowerLevel t →
      (ν : ℝ) + (L : ℝ) = (sourceCoarseGeneration t : ℝ) → 0 < k →
      Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
      q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
      Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * ν →
      (geometricGWRecordLaw k L).real (sourceContinuationWindow t ν L q) ≤
        C * gwBarrierPrefactor L (Real.sqrt (2 * (k : ℝ))) (sourceTerminalRoot t q)
          (4 + sourceBarrierSlope t * ν)
          (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) *
          Real.sqrt (Real.sqrt (2 * (k : ℝ)) / (sourceTerminalRoot t q * L)) := by
  obtain ⟨C, hC, hu⟩ := source_continuation_window_upper hGW
  refine ⟨C, hC, ?_⟩
  filter_upwards [source_continuation_remaining_time, source_continuation_cutoff_reserve,
    source_deficit_large_conditions, eventually_ge_atTop (8 : ℝ)] with t htime hcut ht ht8
  intro q ν L k hν hN hk hq hq2 hx
  have hLhalf : t / 2 ≤ (L : ℝ) := by linarith [htime ν hν]
  have hL : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  have hd1 := sourceLowerTime_ge_one t ht.1
  have hT : (ν : ℝ) + L ≤ sourceTotalTime t := by
    unfold sourceTotalTime
    linarith
  have hν' : (ν : ℝ) ≤ sourceLowerTime (sourceLowerRadius t) := by
    have hc : (ν : ℝ) ≤ 2 * (sourceCoarseLowerLevel t : ℝ) := by exact_mod_cast hν
    exact hc.trans hcut
  have hs := sourceBarrierSlope_bounds t ht.1 ht.2.1
  have hmul := mul_le_mul_of_nonneg_right hs.2 (Nat.cast_nonneg ν : (0 : ℝ) ≤ ν)
  have hy := sourceTerminalRoot_bounds t q ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hq hq2
  have hq0 : 0 ≤ q := (Real.sqrt_nonneg _).trans hq
  apply hu t q ν L k hL hk hN hT
  · linarith [ht.2.2.1]
  · have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by norm_num
    linarith
  · linarith
  · exact hx
  · unfold sourceTerminalRoot
    linarith

end SRWTightness
