import SRWTightness.ActualChildRecords

namespace SRWTightness

/-- Standard finite-word extraction associativity. When the child target and domain are nested
in the parent target and domain and the word ends outside the parent domain, collecting complete
child words inside all complete parents equals collecting them directly, in chronological order.
This explicit deterministic input contains no source scale, probability or estimate. -/
def TwoLevelWordFlatteningInput : Prop :=
  ∀ (K C K' C' : Finset Site), K ⊆ C → K' ⊆ C' → K' ⊆ K → C' ⊆ C →
    ∀ (x : Site) (w : PathWord), x + position (wordPath w) w.length ∉ C →
      (wordChildRecords K C x
        (fun y u ↦ wordChildRecords K' C' y (fun z v ↦ (z, v)) u) w).flatten =
        wordChildRecords K' C' x (fun z v ↦ (z, v)) w

/-- The ordered finite-word identity transfers to every chosen child-record map. -/
theorem word_child_records_flatten (hF : TwoLevelWordFlatteningInput) {M : Type*}
    (K C K' C' : Finset Site) (hKC : K ⊆ C) (hKC' : K' ⊆ C')
    (hK : K' ⊆ K) (hC : C' ⊆ C) (x : Site) (w : PathWord)
    (hend : x + position (wordPath w) w.length ∉ C) (F : Site → PathWord → M) :
    (wordChildRecords K C x (fun y u ↦ wordChildRecords K' C' y F u) w).flatten =
      wordChildRecords K' C' x F w := by
  have hh := congrArg (List.map (fun p : Site × PathWord ↦ F p.1 p.2))
    (hF K C K' C' hKC hKC' hK hC x w hend)
  simpa only [List.map_flatten, wordChildRecords, List.map_map, Function.comp_def] using hh

end SRWTightness
