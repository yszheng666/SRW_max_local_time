import Mathlib.MeasureTheory.MeasurableSpace.Basic

namespace SRWTightness

/-- Every countable singleton-measurable space has the full measurable structure. -/
theorem countable_measurable_space_top (A : Type*) [m : MeasurableSpace A]
    [MeasurableSingletonClass A] [Countable A] : m = ⊤ := by
  apply top_unique
  intro s hs
  exact s.to_countable.measurableSet

end SRWTightness
