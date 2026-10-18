import SRWTightness.ExteriorWordAdmissibility
import SRWTightness.ExteriorWordTripleRenewal
import SRWTightness.ExteriorWordReassembly
import SRWTightness.ExteriorRecordNoVisit
import SRWTightness.AdmissibleWordAppend

namespace SRWTightness

/-- Every legal internal-word tuple can be inserted without changing the retained exterior
record. -/
theorem reassembleExteriorWord_admissible (D K C : Finset Site) (label : Site → Bool)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (x : Site) (h : ExteriorPathRecord)
    (us : List PathWord) (hlen : us.length = h.1.length)
    (hgeom : ExteriorWordAdmissible D K C label x h)
    (hwords : ∀ pair ∈ h.1.zip us,
      AdmissibleExitWord C pair.1.2.2.1 pair.1.2.2.2 pair.2) :
    ∃ e, AdmissibleExitWord D x e (reassembleExteriorWord h us) ∧
      wordExteriorRecord K C label x (reassembleExteriorWord h us) = h ∧
      wordChildRecords K C x (fun _ u ↦ u) (reassembleExteriorWord h us) = us := by
  rcases h with ⟨slots, tail⟩
  induction slots generalizing x us with
  | nil =>
    have hu : us = [] := List.length_eq_zero_iff.mp hlen
    subst us
    rw [ExteriorWordAdmissible] at hgeom
    obtain ⟨⟨e, he⟩, hnone⟩ := hgeom
    refine ⟨e, ?_, ?_, ?_⟩
    · simpa only [reassembleExteriorWord] using he
    · simpa only [reassembleExteriorWord] using wordExteriorRecord_no_visit K C label x tail hnone
    · simpa only [reassembleExteriorWord] using
        wordChildRecords_no_visit K C x (fun _ u ↦ u) tail hnone
  | cons slot slots ih =>
    rcases slot with ⟨p, tag, a, e⟩
    cases us with
    | nil => simp at hlen
    | cons u us =>
      have hl : us.length = slots.length := by simpa using hlen
      rw [ExteriorWordAdmissible] at hgeom
      obtain ⟨hpreD, hpreK, hp, ha, htag, heC, htail⟩ := hgeom
      have hu : AdmissibleExitWord C a e u := hwords ((p, tag, a, e), u) (by simp)
      have hrest : ∀ pair ∈ slots.zip us,
          AdmissibleExitWord C pair.1.2.2.1 pair.1.2.2.2 pair.2 := by
        intro pair hpair
        exact hwords pair (by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr hpair)
      obtain ⟨z, hz, hrec, hchild⟩ := ih e us hl htail hrest
      have hmid := admissibleExitWord_append D a e z u
        (reassembleExteriorWord (slots, tail) us)
        (fun i hi ↦ hCD (hu.1 i hi)) hu.2.1 hz
      have hfull := admissibleExitWord_append D x a z p
        (pathWordAppend u (reassembleExteriorWord (slots, tail) us)) hpreD hp hmid
      obtain ⟨hc, hr⟩ := exterior_word_triple_renewal K C hKC label x a e p u
        (reassembleExteriorWord (slots, tail) us) (fun _ u ↦ u) hpreK hp ha hu
      rw [hchild] at hc
      rw [hrec, ← htag] at hr
      refine ⟨z, ?_, ?_, ?_⟩
      · simpa only [reassembleExteriorWord] using hfull
      · simpa only [reassembleExteriorWord] using hr
      · simpa only [reassembleExteriorWord] using hc

end SRWTightness
