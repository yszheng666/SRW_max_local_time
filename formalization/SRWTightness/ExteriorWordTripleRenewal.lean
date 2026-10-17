import SRWTightness.PathWordTripleChildGeometry
import SRWTightness.PathWordTripleSlices
import SRWTightness.ChildWordExitRenewal
import SRWTightness.ExteriorRecordExitRenewal

namespace SRWTightness

/-- Inserting one legal child preserves its exterior header and the exact subsequent record
lists. -/
theorem exterior_word_triple_renewal {M : Type*} (K C : Finset Site) (hKC : K ⊆ C)
    (label : Site → Bool) (x a e : Site) (p u v : PathWord) (F : Site → PathWord → M)
    (hpre : ∀ i < p.length, x + position (wordPath p) i ∉ K)
    (hp : x + position (wordPath p) p.length = a) (ha : a ∈ K)
    (hu : AdmissibleExitWord C a e u) :
    wordChildRecords K C x F (pathWordAppend p (pathWordAppend u v)) =
        F a u :: wordChildRecords K C e F v ∧
      wordExteriorRecord K C label x (pathWordAppend p (pathWordAppend u v)) =
        let rest := wordExteriorRecord K C label e v
        ((p, label a, a, e) :: rest.1, rest.2) := by
  let w := pathWordAppend p (pathWordAppend u v)
  obtain ⟨hab, hb, hpre', ha', hin, he'⟩ :=
    pathWordTriple_child_geometry K C hKC x a e p u v hpre hp ha hu
  have henter : x + position (wordPath w) p.length ∈ K := by rw [ha']; exact ha
  have hexit : x + position (wordPath w) (p.length + u.length) ∉ C := by
    rw [he']; exact hu.2.2
  have hc := wordChildRecords_exit_renewal K C hKC x w F p.length
    (p.length + u.length) hab hb hpre' henter hin hexit
  have hr := wordExteriorRecord_exit_renewal K C hKC label x w p.length
    (p.length + u.length) hab hb hpre' henter hin hexit
  dsimp only [w] at hc hr
  simp only [ha', he', pathWordAppend_slice_middle, pathWordAppend_slice_final,
    pathWordAppend_slice_left] at hc hr
  exact ⟨hc, hr⟩

end SRWTightness
