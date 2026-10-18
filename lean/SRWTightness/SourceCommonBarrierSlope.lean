import SRWTightness.SourceCommonPairLevelRange
import SRWTightness.SourceBarrierSlopeError
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology
namespace SRWTightness

/-- The slope is eventually below two, and its error times every common barrier dent is bounded. -/
theorem source_common_barrier_slope :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ,
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      0 ≤ sourceBarrierSlope t ∧ sourceBarrierSlope t ≤ 2 ∧
      |sourceBarrierSlope t - 2| *
        (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) ≤ 1 := by
  have hlog : Tendsto (fun t : ℝ ↦ Real.log t / t ^ (3 / 5 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)).tendsto_div_nhds_zero
  have hc : Tendsto (fun t : ℝ ↦ (2 * sourceTotalTimeError) / t ^ (3 / 5 : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num))
  have hsum := (tendsto_order.1 (hc.add hlog)).2 (1 / 2) (by norm_num)
  filter_upwards [hsum, source_common_pair_level_range,
    eventually_ge_atTop (sourceScaleThreshold 4), eventually_ge_atTop (2 * sourceTotalTimeError),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 * sourceTotalTimeError))]
    with t hs hr ht htE hl
  intro j hd
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 < t := by linarith
  have hT := sourceTotalTime_ge_half t ht htE
  have hT0 : 0 < sourceTotalTime t := by linarith
  have he := abs_le.mp (sourceTotalTime_error t ht)
  have hθ2 : sourceBarrierSlope t ≤ 2 := by
    unfold sourceBarrierSlope sourceTerminalHeight
    apply (div_le_iff₀ hT0).mpr
    linarith
  refine ⟨(sourceBarrierSlope_bounds t ht htE).1, hθ2, ?_⟩
  have hj := hr j hd
  have hw0 : 0 ≤ min (j : ℝ) (sourceTotalTime t - j) := le_min (Nat.cast_nonneg _) (by linarith)
  have hw := Real.rpow_le_rpow hw0 ((min_le_left _ _).trans hj.1)
    (by norm_num : (0 : ℝ) ≤ 2 / 5)
  have hp : 0 < t ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hnum : 2 * (2 * sourceTotalTimeError + Real.log t) ≤ t ^ (3 / 5 : ℝ) := by
    rw [← add_div] at hs
    have hh := (div_lt_iff₀ hp).mp hs
    linarith
  have herr := (sourceBarrierSlope_error t ht htE).trans
    (div_le_div_of_nonneg_right hnum ht0.le)
  calc
    _ ≤ (t ^ (3 / 5 : ℝ) / t) * t ^ (2 / 5 : ℝ) :=
      mul_le_mul herr hw (Real.rpow_nonneg hw0 _) (by positivity)
    _ = 1 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add ht0]
      norm_num [ht0.ne']

end SRWTightness
