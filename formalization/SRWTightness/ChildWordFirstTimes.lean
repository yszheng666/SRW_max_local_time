import SRWTightness.ChildRangeRenewal

namespace SRWTightness

/-- Any entrance before an outside word endpoint has a first entrance and first following exit. -/
theorem word_first_child_times (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (hend : x + position (wordPath w) w.length ∉ C)
    (hvisit : ∃ i < w.length, x + position (wordPath w) i ∈ K) :
    ∃ a b : ℕ, a < b ∧ b ≤ w.length ∧
      (∀ i < a, x + position (wordPath w) i ∉ K) ∧
      x + position (wordPath w) a ∈ K ∧
      (∀ i, a < i → i < b → x + position (wordPath w) i ∈ C) ∧
      x + position (wordPath w) b ∉ C := by
  let a := Nat.find hvisit
  have ha := Nat.find_spec hvisit
  change a < w.length ∧ x + position (wordPath w) a ∈ K at ha
  have hpre : ∀ i < a, x + position (wordPath w) i ∉ K := by
    intro i hi hmem
    have hn := Nat.find_min hvisit hi
    exact hn ⟨hi.trans ha.1, hmem⟩
  have hex : ∃ b : ℕ, a < b ∧ b ≤ w.length ∧
      x + position (wordPath w) b ∉ C := ⟨w.length, ha.1, le_rfl, hend⟩
  let b := Nat.find hex
  have hb := Nat.find_spec hex
  change a < b ∧ b ≤ w.length ∧ x + position (wordPath w) b ∉ C at hb
  refine ⟨a, b, hb.1, hb.2.1, hpre, ha.2, ?_, hb.2.2⟩
  intro i hai hib
  by_contra hout
  exact Nat.find_min hex hib ⟨hai, hib.le.trans hb.2.1, hout⟩

end SRWTightness
