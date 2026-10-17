import SRWTightness.SourceWalkSuccessEvent

open MeasureTheory
namespace SRWTightness

/-- Every forward population coordinate is a measurable function of the actual stopped word. -/
theorem measurable_sourceForwardRecordCount (m r : ℝ) (ℓ k i : ℕ) (b : Site)
    (D : Finset Site) (x : Site) : Measurable (sourceForwardRecordCount m r ℓ k i b D x) :=
  measurable_killed_word_record D x
    (fun w ↦ (terminalWordRecords (sourceExcursionLevels m r ℓ b k (i - k + 1)) x w).length)

/-- The manuscript count retains the common original walk as its probability-space argument. -/
theorem measurable_sourceActualCount (t : ℝ) (b : Site) (j : ℕ) :
    Measurable (sourceActualCount t b j) :=
  measurable_sourceForwardRecordCount _ _ _ _ _ _ _ _

end SRWTightness
