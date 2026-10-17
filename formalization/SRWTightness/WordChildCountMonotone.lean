import SRWTightness.ChildVisitUniqueness
import SRWTightness.ChildIntervalInterior
import Mathlib.Data.Finset.Card

namespace SRWTightness

/-- Two members of a separated list are equal or occur in one of the two strict time orders. -/
theorem separated_intervals_order (rs : List (ℕ × ℕ))
    (hs : rs.Pairwise (fun a b ↦ a.2 < b.1))
    (a b : ℕ × ℕ) (ha : a ∈ rs) (hb : b ∈ rs) :
    a = b ∨ a.2 < b.1 ∨ b.2 < a.1 := by
  induction rs with
  | nil => simp at ha
  | cons q rs ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp ha with he | ha
    · subst a
      rcases List.mem_cons.mp hb with he | hb
      · exact Or.inl he.symm
      · exact Or.inr (Or.inl (hh b hb))
    · rcases List.mem_cons.mp hb with he | hb
      · subst b
        exact Or.inr (Or.inr (hh a ha))
      · exact ih ht ha hb

/-- Expanding the inner set and shrinking the outer set increases complete traversal counts.
The proof injects old entrances into covering intervals of the new extractor. -/
theorem wordChildIntervals_length_mono (K₁ C₁ K₂ C₂ : Finset Site)
    (hK : K₁ ⊆ K₂) (hKC : K₂ ⊆ C₂) (hC : C₂ ⊆ C₁)
    (x : Site) (w : PathWord) :
    (wordChildIntervals K₁ C₁ x w).length ≤ (wordChildIntervals K₂ C₂ x w).length := by
  classical
  let A := wordChildIntervals K₁ C₁ x w
  let B := wordChildIntervals K₂ C₂ x w
  have hpos : ∀ q ∈ A, q.1 < q.2 := by
    intro q hq
    exact scanChildIntervals_start_lt_end K₁ C₁ x (wordPath w) _
      List.pairwise_lt_range none (by intro a he; cases he) q hq
  have hsep : A.Pairwise (fun a b ↦ a.2 < b.1) :=
    scanChildIntervals_separated K₁ C₁ x (wordPath w) _ List.pairwise_lt_range none
  have hnodup : A.Nodup := hsep.imp_of_mem (by
    intro a b ha hb hab he
    subst b
    have hp := hpos a ha
    omega)
  have hcover : ∀ q ∈ A, ∃ p ∈ B, p.1 ≤ q.1 ∧ q.1 < p.2 := by
    intro q hq
    have ht := wordChildIntervals_endpoint_le K₁ C₁ x w q hq
    have he := wordChildIntervals_endpoints K₁ C₁ x w q hq
    apply scanChildIntervals_cover_visit K₂ C₂ hKC x (wordPath w)
      (List.range (w.length + 1)) List.pairwise_lt_range none q.1
    · exact List.mem_range.mpr (by omega)
    · exact hK he.1
    · intro a heq
      cases heq
    · exact ⟨q.2, List.mem_range.mpr (by omega), hpos q hq, fun hc ↦ he.2 (hC hc)⟩
  let f : A.toFinset → B.toFinset := fun q ↦
    ⟨Classical.choose (hcover q (List.mem_toFinset.mp q.property)),
      List.mem_toFinset.mpr (Classical.choose_spec
        (hcover q (List.mem_toFinset.mp q.property))).1⟩
  have hf : ∀ q : A.toFinset, (f q).val.1 ≤ q.val.1 ∧ q.val.1 < (f q).val.2 := by
    intro q
    exact (Classical.choose_spec (hcover q (List.mem_toFinset.mp q.property))).2
  have hdistinct : ∀ a ∈ A, ∀ b ∈ A, a.2 < b.1 → ∀ p ∈ B,
      p.1 ≤ a.1 → b.1 < p.2 → False := by
    intro a ha b hb hab p hp hpa hbp
    have hapos := hpos a ha
    have hin := wordChildIntervals_interior K₂ C₂ hKC x w p hp a.2
      (by omega) (by omega)
    exact (wordChildIntervals_endpoints K₁ C₁ x w a ha).2 (hC hin)
  have hinj : Function.Injective f := by
    intro a b he
    have ha := List.mem_toFinset.mp a.property
    have hb := List.mem_toFinset.mp b.property
    have hfa := hf a
    have hfb := hf b
    have hp := List.mem_toFinset.mp (f a).property
    rw [← he] at hfb
    rcases separated_intervals_order A hsep a b ha hb with hab | hab | hba
    · exact Subtype.ext hab
    · exact (hdistinct a ha b hb hab (f a) hp hfa.1 hfb.2).elim
    · exact (hdistinct b hb a ha hba (f a) hp hfb.1 hfa.2).elim
  calc
    A.length = A.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ B.toFinset.card := Finset.card_le_card_of_injective hinj
    _ ≤ B.length := List.toFinset_card_le B

/-- The finite-word traversal comparison applies pathwise to the actual killed walk. -/
theorem killedChildIntervals_length_mono (D K₁ C₁ K₂ C₂ : Finset Site)
    (hK : K₁ ⊆ K₂) (hKC : K₂ ⊆ C₂) (hC : C₂ ⊆ C₁) (x : Site) (ω : Sample) :
    (killedChildIntervals D K₁ C₁ x ω).length ≤
      (killedChildIntervals D K₂ C₂ x ω).length :=
  wordChildIntervals_length_mono K₁ C₁ K₂ C₂ hK hKC hC x (killedPathWord D x ω)

end SRWTightness
