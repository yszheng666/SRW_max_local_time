import SRWTightness.ExternalWordFlattening

open MeasureTheory
namespace SRWTightness

/-- Nested extraction can be grouped by complete parent segments of the original killed walk. -/
theorem killed_child_records_flatten (hF : TwoLevelWordFlatteningInput) {M : Type*}
    (D K C K' C' : Finset Site) (hKC : K ⊆ C) (hKC' : K' ⊆ C')
    (hK : K' ⊆ K) (hC : C' ⊆ C) (hCD : C ⊆ D) (x : Site)
    (F : Site → PathWord → M) :
    (fun ω ↦ (killedChildRecords D K C x
      (fun y u ↦ wordChildRecords K' C' y F u) ω).flatten) =ᵐ[pathLaw]
      killedChildRecords D K' C' x F := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hfin
  exact word_child_records_flatten hF K C K' C' hKC hKC' hK hC x
    (killedPathWord D x ω) (killedPathWord_endpoint_outside_child D C hCD x ω hfin) F

/-- Projecting the ordered entrance/word pairs gives the selected actual record list. -/
theorem killed_child_word_pairs_map {M : Type*} (D K C : Finset Site) (x : Site)
    (F : Site → PathWord → M) (ω : Sample) :
    ((killedChildRecords D K C x (fun y u ↦ (y, u)) ω).map (fun p ↦ F p.1 p.2)) =
      killedChildRecords D K C x F ω := by
  simp only [killedChildRecords, wordChildRecords, List.map_map, Function.comp_def]

end SRWTightness
