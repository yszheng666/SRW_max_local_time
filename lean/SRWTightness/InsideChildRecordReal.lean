import SRWTightness.InsideChildRecord

open MeasureTheory
namespace SRWTightness

/-- The first short root is certain at an inner entrance; its record remains coupled to its exit. -/
theorem killedChildRecords_inside_cons_probability_real (D K C : Finset Site)
    (hKC : K ⊆ C) (hCD : C ⊆ D) {R : Type*} (x : Site) (hx : x ∈ K)
    (F : Site → PathWord → R) (r : R) (rs : List R) :
    pathLaw.real {ω | killedChildRecords D K C x F ω = r :: rs} =
      ∫ ξ, pathLaw.real {ω | killedChildRecords D K C ξ F ω = rs}
        ∂recordExitSlice C x (fun ω ↦ F x (killedPathWord C x ω)) r := by
  change (pathLaw {ω | killedChildRecords D K C x F ω = r :: rs}).toReal =
    ∫ ξ, (pathLaw {ω | killedChildRecords D K C ξ F ω = rs}).toReal
      ∂recordExitSlice C x (fun ω ↦ F x (killedPathWord C x ω)) r
  rw [killedChildRecords_inside_cons_probability D K C hKC hCD x hx F r rs]
  exact (integral_toReal (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall (fun ξ ↦ measure_lt_top pathLaw
      {ω | killedChildRecords D K C ξ F ω = rs}))).symm

end SRWTightness
