import SRWTightness.ContinuationTerminalExponent
import SRWTightness.SourceTimePowerDecay

open Filter
namespace SRWTightness

/-- Uniform cancellation of the terminal deficit in the actual early continuation range. -/
theorem source_continuation_terminal_exponent :
    ∀ᶠ t : ℝ in atTop, ∀ (ν L : ℕ) (x q : ℝ),
      ν ≤ 2 * sourceCoarseLowerLevel t →
      (ν : ℝ) + (L : ℝ) = (sourceCoarseGeneration t : ℝ) → 0 ≤ x →
      Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
      q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
      -((x - sourceTerminalRoot t q) ^ 2 / (2 * (L : ℝ))) - 2 * q ≤
        -((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - x) ^ 2 /
          (2 * (L : ℝ))) + 1 := by
  have hsmall := (tendsto_order.1 (sourceLowerTime_pow_div_t_tendsto_zero 2)).2
    (1 / 8 : ℝ) (by norm_num)
  filter_upwards [source_continuation_cutoff_reserve, source_continuation_remaining_time,
    source_deficit_large_conditions, hsmall,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 * sourceTotalTimeError))]
    with t hc htime ht hsmall hlog
  intro ν L x q hν hN hx hq hq2
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  have ht0 : 0 < t := by linarith
  have hL : t / 2 ≤ (L : ℝ) := by linarith [htime ν hν]
  have hd1 := sourceLowerTime_ge_one t ht.1
  have hνd : (ν : ℝ) ≤ sourceLowerTime (sourceLowerRadius t) := by
    have hh : (ν : ℝ) ≤ 2 * (sourceCoarseLowerLevel t : ℝ) := by exact_mod_cast hν
    exact hh.trans hc
  have hT := sourceTotalTime_ge_half t ht.1 ht.2.1
  have hTerr := (abs_le.mp (sourceTotalTime_error t ht.1)).1
  have hθ : sourceBarrierSlope t ≤ 2 := by
    unfold sourceBarrierSlope sourceTerminalHeight
    apply (div_le_iff₀ (show 0 < sourceTotalTime t by linarith)).mpr
    linarith
  have hqd : q ≤ 2 * sourceLowerTime (sourceLowerRadius t) := by
    linarith [Real.sqrt_le_self_iff.mpr (Or.inr hd1)]
  have hdsmall : 8 * sourceLowerTime (sourceLowerRadius t) ^ 2 ≤ t := by
    have hh := (div_lt_iff₀ ht0).mp hsmall
    linarith
  exact continuation_terminal_exponent t (L : ℝ) (sourceCoarseGeneration t : ℝ)
    (ν : ℝ) (sourceBarrierSlope t) x q (sourceLowerTime (sourceLowerRadius t)) ht0 hL hN
    (Nat.cast_nonneg _) hνd hθ hx ((Real.sqrt_nonneg _).trans hq) hqd hdsmall

end SRWTightness
