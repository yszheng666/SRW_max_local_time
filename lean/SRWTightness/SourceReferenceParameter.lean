import SRWTightness.SourceLongEscapeProbability
import SRWTightness.SourceExteriorEntranceShell

open Filter
namespace SRWTightness

/-- The source parameter belongs to (0,1) once its actual inner radius dominates the buffer. -/
theorem source_reference_parameter_mem (t : ℝ) (ν J : ℕ)
    (hm : 70 ≤ sourceLowerRadius t)
    (hν : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (hJ : 1 ≤ J) :
    0 < sourceLongEscapeParameter (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J ∧
    sourceLongEscapeParameter (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J < 1 := by
  have hrad := sourceRecordRadius_ge_terminal (sourceLowerRadius t) (sourceLowerRadius_pos t).le
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) hν
  apply buffered_long_escape_parameter_pos_lt_one
  · exact (sourceLowerRadius_pos t).trans_le hrad
  · norm_num [sourceRecordBuffer]
  · norm_num [sourceRecordBuffer]
    linarith
  · exact_mod_cast hJ

/-- Every early source continuation level has a genuine geometric reference parameter uniformly. -/
theorem source_reference_parameter_early :
    ∀ᶠ t : ℝ in atTop, ∀ ν J : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t → 1 ≤ J →
      0 < sourceLongEscapeParameter (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J ∧
      sourceLongEscapeParameter (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J < 1 := by
  filter_upwards [source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (70 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hN htime hm ht
  intro ν J hν hJ
  have hnreal : (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by exact_mod_cast hnreal
  apply source_reference_parameter_mem t ν J hm _ hJ
  have hp := hN.1
  omega

end SRWTightness
