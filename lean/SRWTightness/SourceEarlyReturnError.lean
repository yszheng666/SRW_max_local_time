import SRWTightness.SourceDecouplingExponent
import SRWTightness.SourceContinuationRange
import SRWTightness.SourceRootGWHorizon

open Filter
namespace SRWTightness

/-- Uniformly over the original early continuation range, the return-count cost vanishes at
least as fast as the fifth inverse power of the source time. -/
theorem source_early_return_error :
    ∀ᶠ t : ℝ in atTop, ∀ ν : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
      ∀ C : ℝ, 0 ≤ C →
      16 * ((ν : ℝ) + 1) ^ 2 *
        (C * 15 / (sourceRecordRadius (sourceLowerRadius t)
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) ≤
        1920 * C / t ^ 5 := by
  filter_upwards [source_continuation_cutoff_reserve, source_deficit_large_conditions,
    source_continuation_remaining_time, source_root_gw_horizon_large,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (28 : ℝ))]
    with t hreserve ht htime hN hm
  intro ν hν C hC
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  have ht0 : 0 < t := by linarith
  have hνr : (ν : ℝ) ≤ 2 * (sourceCoarseLowerLevel t : ℝ) := by exact_mod_cast hν
  have hνt : (ν : ℝ) ≤ t := by linarith [ht.2.2.1]
  have hnreal : (ν : ℝ) ≤
      ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by
    exact_mod_cast hnreal
  have hdepth : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hp := hN.1
    omega
  let m := sourceLowerRadius t
  let r := sourceRecordRadius m (sourceRootDepth (Real.exp t) m) (ν + 1)
  have hrad : m ≤ r := sourceRecordRadius_ge_terminal m (sourceLowerRadius_pos t).le _ _ hdepth
  have hm0 : 0 < m := sourceLowerRadius_pos t
  have hden : m / 2 ≤ r - 14 := by
    have hm' : 28 ≤ m := hm
    linarith
  have hd0 : 0 < r - 14 := lt_of_lt_of_le (by positivity : 0 < m / 2) hden
  have hfrac : C * 15 / (r - 14) ≤ 30 * C / m := by
    calc
      _ ≤ C * 15 / (m / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by field_simp [hm0.ne'] <;> ring
  have hsq : ((ν : ℝ) + 1) ^ 2 ≤ 4 * t ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (ν : ℝ) + 1)
      (show (ν : ℝ) + 1 ≤ 2 * t by linarith) 2
    nlinarith only [hh]
  have hmajor : t ^ 2 / m ≤ 1 / t ^ 5 := by
    have hh := div_le_div_of_nonneg_left (sq_nonneg t) (pow_pos ht0 7)
      (sourceLowerRadius_ge_seventh_power t ht.1)
    exact hh.trans_eq (by field_simp [ht0.ne'])
  change 16 * ((ν : ℝ) + 1) ^ 2 * (C * 15 / (r - 14)) ≤ _
  calc
    _ ≤ 16 * (4 * t ^ 2) * (C * 15 / (r - 14)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (div_nonneg (by positivity) hd0.le)
    _ ≤ 16 * (4 * t ^ 2) * (30 * C / m) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = (1920 * C) * (t ^ 2 / m) := by ring
    _ ≤ (1920 * C) * (1 / t ^ 5) :=
      mul_le_mul_of_nonneg_left hmajor (by positivity)
    _ = _ := by ring

end SRWTightness
