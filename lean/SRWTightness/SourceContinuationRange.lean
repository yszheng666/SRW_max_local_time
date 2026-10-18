import SRWTightness.SourceCommonDentLower
import SRWTightness.SourceDeficitBand

open Filter
namespace SRWTightness

/-- The entire early continuation range is smaller than the terminal time reserve. -/
theorem source_continuation_cutoff_reserve :
    ∀ᶠ t : ℝ in atTop,
      2 * (sourceCoarseLowerLevel t : ℝ) ≤ sourceLowerTime (sourceLowerRadius t) := by
  filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4),
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (sourceLowerTimeError + 3))] with t ht hl
  have hE := sourceLowerTimeError_pos
  have hl1 : 1 ≤ Real.log t := by linarith
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1
  have hd := (abs_le.mp (sourceLowerTime_log_bound (sourceLowerRadius t)
    (by linarith))).1
  have hp := Real.rpow_le_rpow_of_exponent_le
    (by linarith : 1 ≤ 1000 * Real.log t) (by norm_num : (1 : ℝ) ≤ 5 / 2)
  rw [Real.rpow_one] at hp
  have htwo := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (2 : ℝ) ≤ 5 / 2)
  rw [Real.rpow_two] at htwo
  have hgrowth : 4 * (1000 * Real.log t) ^ (5 / 2 : ℝ) ≤
      Real.log (sourceLowerRadius t) := by
    rw [log_sourceLowerRadius, sourceLowerLogRadius,
      show 2000 * Real.log t = 2 * (1000 * Real.log t) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ 1000 * Real.log t)]
    exact mul_le_mul_of_nonneg_right (by norm_num at htwo ⊢; exact htwo)
      (by positivity)
  have hc : (sourceCoarseLowerLevel t : ℝ) <
      (1000 * Real.log t) ^ (5 / 2 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  linarith

/-- Early continuation leaves at least half of the original time for the GW estimate. -/
theorem source_continuation_remaining_time :
    ∀ᶠ t : ℝ in atTop, ∀ ν : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
      t / 2 ≤ (sourceCoarseGeneration t : ℝ) - ν := by
  filter_upwards [source_continuation_cutoff_reserve, source_deficit_large_conditions,
    eventually_ge_atTop (4 * sourceTotalTimeError)] with t hc ht hE
  intro ν hν
  have hν' : (ν : ℝ) ≤ 2 * (sourceCoarseLowerLevel t : ℝ) := by exact_mod_cast hν
  have herr := (abs_le.mp (sourceTotalTime_error t ht.1)).1
  have hd := ht.2.2.1
  have hpos := sourceTotalTimeError_pos
  unfold sourceTotalTime at herr
  linarith

end SRWTightness
