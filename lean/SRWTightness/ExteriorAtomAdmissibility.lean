import SRWTightness.ExteriorWordAdmissibleActual
import SRWTightness.KilledWordBridgeSupport
import SRWTightness.PositiveAtomSupport

open MeasureTheory
namespace SRWTightness

/-- Positive actual exterior atoms inherit all local geometric constraints required for
reinsertion. -/
theorem exterior_atom_admissible (D K C : Finset Site) (label : Site → Bool)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (x : Site) (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D K C label x ω = h}) :
    ExteriorWordAdmissible D K C label x h := by
  apply support_of_positive_atom pathLaw (killedExteriorRecord D K C label x)
    (ExteriorWordAdmissible D K C label x) ?_ h hh
  filter_upwards [killed_word_admissible D x] with ω hω
  exact exteriorWordAdmissible_actual D K C label hKC hCD x
    (domainExitLocation D x ω) (killedPathWord D x ω) hω

end SRWTightness
