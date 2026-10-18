import SRWTightness.ChildIntervalExtraction

open MeasureTheory

namespace SRWTightness

/-- The actual complete-child count is a measurable function of the killed finite word. -/
theorem measurable_killed_child_count (D K C : Finset Site) (x : Site) :
    Measurable (fun ω ↦ (killedChildIntervals D K C x ω).length) :=
  measurable_killed_word_record D x (fun w ↦ (wordChildIntervals K C x w).length)

/-- The finite scan bounds the number of complete children by inspected killed-walk times. -/
theorem killed_child_count_le_steps (D K C : Finset Site) (x : Site) (ω : Sample) :
    (killedChildIntervals D K C x ω).length ≤ domainSteps D x ω + 1 := by
  simpa only [killedChildIntervals, wordChildIntervals, List.length_range,
    killedPathWord] using scanChildIntervals_length_le K C x
      (wordPath (killedPathWord D x ω)) (List.range ((killedPathWord D x ω).length + 1)) none

/-- The count of actual complete children is integrable for every finite killed domain. -/
theorem integrable_killed_child_count (D K C : Finset Site) (x : Site) :
    Integrable (fun ω ↦ ((killedChildIntervals D K C x ω).length : ℝ)) pathLaw := by
  apply ((integrable_domainSteps D x).add (integrable_const (1 : ℝ))).mono_nonneg
    (((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_killed_child_count D K C x)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun ω ↦ Nat.cast_nonneg _)
  · apply Filter.Eventually.of_forall
    intro ω
    change ((killedChildIntervals D K C x ω).length : ℝ) ≤ (domainSteps D x ω : ℝ) + 1
    exact_mod_cast killed_child_count_le_steps D K C x ω

end SRWTightness
