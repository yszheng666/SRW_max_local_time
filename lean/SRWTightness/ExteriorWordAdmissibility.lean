import SRWTightness.ExteriorPathRecord
import SRWTightness.ExternalStoppedWordMass

namespace SRWTightness

/-- Local geometric conditions on retained exterior pieces, independent of deleted durations. -/
def ExteriorWordAdmissible (D K C : Finset Site) (label : Site → Bool) :
    Site → ExteriorPathRecord → Prop
  | x, ([], tail) =>
      (∃ e, AdmissibleExitWord D x e tail) ∧
        ∀ i ≤ tail.length, x + position (wordPath tail) i ∉ K
  | x, (slot :: slots, tail) =>
      (∀ i < slot.1.length, x + position (wordPath slot.1) i ∈ D) ∧
      (∀ i < slot.1.length, x + position (wordPath slot.1) i ∉ K) ∧
      x + position (wordPath slot.1) slot.1.length = slot.2.2.1 ∧
      slot.2.2.1 ∈ K ∧ slot.2.1 = label slot.2.2.1 ∧ slot.2.2.2 ∉ C ∧
      ExteriorWordAdmissible D K C label slot.2.2.2 (slots, tail)

end SRWTightness
