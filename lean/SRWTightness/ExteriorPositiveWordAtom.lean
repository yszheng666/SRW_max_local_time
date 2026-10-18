import SRWTightness.ExteriorPathRecord
import SRWTightness.PositiveAtomSupport

open MeasureTheory
namespace SRWTightness

/-- Every positive exterior atom contains a positive atom of its complete internal words. -/
theorem exterior_positive_word_atom (D K C : Finset Site) (label : Site → Bool)
    (x : Site) (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D K C label x ω = h}) :
    ∃ us : List PathWord, us.length = h.1.length ∧
      0 < pathLaw.real {ω | killedChildRecords D K C x (fun _ w ↦ w) ω = us ∧
        killedExteriorRecord D K C label x ω = h} := by
  let f := fun ω ↦ (killedChildRecords D K C x (fun _ w ↦ w) ω,
    killedExteriorRecord D K C label x ω)
  have hf := ae_support_of_positive_atoms pathLaw f
    (fun r ↦ 0 < pathLaw.real {ω | f ω = r}) (fun _ hr ↦ hr)
  apply support_of_positive_atom pathLaw (killedExteriorRecord D K C label x)
    (fun r ↦ ∃ us : List PathWord, us.length = r.1.length ∧
      0 < pathLaw.real {ω | killedChildRecords D K C x (fun _ w ↦ w) ω = us ∧
        killedExteriorRecord D K C label x ω = r}) ?_ h hh
  filter_upwards [hf] with ω hω
  refine ⟨_, (killedExteriorRecord_length D K C label x ω).symm, ?_⟩
  simpa only [f, Prod.mk.injEq] using hω

end SRWTightness
