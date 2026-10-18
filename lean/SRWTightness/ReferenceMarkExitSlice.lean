import SRWTightness.RecordExitSlice
import SRWTightness.ReferenceMark

open MeasureTheory

namespace SRWTightness

/-- The actual terminal mark/exit slice has the existing killed-mark probability as its marginal. -/
theorem killedMark_recordExitSlice_mass (D K : Finset Site) (x : Site) (Y : Mark K) :
    (recordExitSlice D x (killedMark D K x) Y).real Set.univ =
      (killedMarkLaw D K x).real {Y} := by
  rw [recordExitSlice_mass, killedMarkLaw,
    map_measureReal_apply (measurable_killedMark D K x) (measurableSet_singleton Y)]
  rfl

end SRWTightness
