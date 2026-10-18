import SRWTightness.SourceOrderedPrefixEvent

open MeasureTheory

namespace SRWTightness

/-- The original prefix is measurable through its finite ordered-record representation. -/
theorem measurableSet_sourceEarlyPrefixEvent (t : ℝ) (b : Site) (j : ℕ) :
    MeasurableSet (sourceEarlyPrefixEvent t b j) := by
  let m := sourceCommonPairInnerRadius t j
  let F := actualFiniteWordRecord (growingRecordEntrance b m 14) (growingRecordExit b m 14)
    (firstEntranceWordOfWord (growingRecordExit b m 14 0) ∅) j
  let S : Set PathWord := {w | ∃ r ∈ sourceOrderedPrefixRecords t j,
    wordChildRecords (growingRecordEntrance b m 14 j) (growingRecordExit b m 14 j) 0 F w = [r]}
  have he : sourceEarlyPrefixEvent t b j = killedPathWord (diskFinset (Real.exp t)) 0 ⁻¹' S := by
    ext ω
    exact source_ordered_prefix_event_iff t b ∅ j ω
  rw [he]
  exact (measurable_killedPathWord _ _) S.to_countable.measurableSet

end SRWTightness
