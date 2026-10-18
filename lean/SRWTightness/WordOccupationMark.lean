import SRWTightness.KilledPathWord
import SRWTightness.ReferenceMark

open MeasureTheory

namespace SRWTightness

/-- The occupation mark retained by a finite excursion word, with its actual entrance point. -/
noncomputable def wordOccupationMark (K : Finset Site) (x : Site) (w : PathWord) : Mark K :=
  fun y ↦ localTime (wordPath w) w.length ((y : Site) - x)

/-- The recorded finite word preserves exactly the actual killed occupation mark. -/
theorem wordOccupationMark_killedPathWord (D K : Finset Site) (x : Site) (ω : Sample) :
    wordOccupationMark K x (killedPathWord D x ω) = killedMark D K x ω := by
  funext y
  exact killedPathWord_localTime D x y ω

/-- Finite-word terminal mark events have the actual killed-mark probability. -/
theorem wordOccupationMark_event_probability (D K : Finset Site) (x : Site)
    (s : Set (Mark K)) (hs : MeasurableSet s) :
    pathLaw.real {ω | wordOccupationMark K x (killedPathWord D x ω) ∈ s} =
      (killedMarkLaw D K x).real s := by
  rw [killedMarkLaw, map_measureReal_apply (measurable_killedMark D K x) hs]
  congr 1
  ext ω
  simp only [wordOccupationMark_killedPathWord, Set.mem_preimage, Set.mem_setOf_eq]

end SRWTightness
