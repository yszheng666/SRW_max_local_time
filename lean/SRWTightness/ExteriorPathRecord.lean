import SRWTightness.ActualChildRecords

open MeasureTheory
namespace SRWTightness

/-- Each deleted segment is represented by its preceding exterior word, label, entrance and exit. -/
abbrev ExteriorSlot := PathWord × Bool × Site × Site

/-- The final exterior word follows all deleted segments; no deleted durations or absolute times occur. -/
abbrev ExteriorPathRecord := List ExteriorSlot × PathWord

/-- Erase complete child intervals while retaining the exterior direction words and endpoint headers. -/
def packExteriorRecord (label : Site → Bool) (x : Site) (w : PathWord) :
    ℕ → List (ℕ × ℕ) → ExteriorPathRecord
  | previous, [] => ([], slicePathWord w previous w.length)
  | previous, (a, b) :: intervals =>
      let tail := packExteriorRecord label x w b intervals
      let entrance := x + position (wordPath w) a
      ((slicePathWord w previous a, label entrance, entrance,
        x + position (wordPath w) b) :: tail.1, tail.2)

/-- The chronological exterior record associated with entrances into K and exits from C. -/
def wordExteriorRecord (K C : Finset Site) (label : Site → Bool) (x : Site)
    (w : PathWord) : ExteriorPathRecord :=
  packExteriorRecord label x w 0 (wordChildIntervals K C x w)

/-- The exterior record of the actual killed SRW. For two separated long balls, K and C are their unions. -/
noncomputable def killedExteriorRecord (D K C : Finset Site) (label : Site → Bool)
    (x : Site) (ω : Sample) : ExteriorPathRecord :=
  wordExteriorRecord K C label x (killedPathWord D x ω)

/-- Conditional records may be formed in the countable exterior space. -/
theorem measurable_killedExteriorRecord [MeasurableSpace ExteriorPathRecord] (D K C : Finset Site) (label : Site → Bool)
    (x : Site) : Measurable (killedExteriorRecord D K C label x) :=
  measurable_killed_word_record D x (wordExteriorRecord K C label x)

/-- Every erased interval contributes exactly one header to the exterior record. -/
theorem packExteriorRecord_length (label : Site → Bool) (x : Site) (w : PathWord)
    (intervals : List (ℕ × ℕ)) (previous : ℕ) :
    (packExteriorRecord label x w previous intervals).1.length = intervals.length := by
  induction intervals generalizing previous with
  | nil => rfl
  | cons q intervals ih =>
    rcases q with ⟨a, b⟩
    simp only [packExteriorRecord, List.length_cons, ih]

/-- Exterior headers and the actual complete internal words have the same number and order of slots. -/
theorem killedExteriorRecord_length (D K C : Finset Site) (label : Site → Bool)
    (x : Site) (ω : Sample) :
    (killedExteriorRecord D K C label x ω).1.length =
      (killedChildRecords D K C x (fun _ w ↦ w) ω).length := by
  simp only [killedExteriorRecord, wordExteriorRecord, packExteriorRecord_length,
    killedChildRecords, wordChildRecords, List.length_map]

end SRWTightness
