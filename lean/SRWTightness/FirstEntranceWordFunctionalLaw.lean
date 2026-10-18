import SRWTightness.FirstEntranceWordFunctional

open MeasureTheory

namespace SRWTightness

/-- Events extracted from the finite parent word have the actual first-entry mark law. -/
theorem firstEntranceWordOfWord_event (D K : Finset Site) (x : Site)
    (s : Set WordMark) (hs : MeasurableSet s) :
    pathLaw.real {ω | firstEntranceWordOfWord D K x (killedPathWord D x ω) ∈ s} =
      (firstEntranceWordMarkLaw D K x).real s := by
  rw [firstEntranceWordMarkLaw,
    map_measureReal_apply (measurable_firstEntranceWordMark D K x) hs]
  apply measureReal_congr
  filter_upwards [firstEntranceWordOfWord_killedPathWord_ae D K x] with ω hω
  change (_ ∈ s) = (_ ∈ s)
  rw [hω]

end SRWTightness
