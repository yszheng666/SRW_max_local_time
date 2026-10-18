import SRWTightness.ChildIntervalExtraction

namespace SRWTightness

/-- Excursion counts depend on observed sites and the pending flag, not on time labels. -/
theorem scanChildIntervals_length_congr (K C : Finset Site)
    (x y : Site) (ω η : Sample) (ts us : List ℕ) (s t : Option ℕ)
    (hloc : ts.map (fun i ↦ x + position ω i) = us.map (fun i ↦ y + position η i))
    (hs : s.isSome = t.isSome) :
    (scanChildIntervals K C x ω s ts).length =
      (scanChildIntervals K C y η t us).length := by
  induction ts generalizing us s t with
  | nil =>
    have hu : us = [] := by simpa using (List.map_eq_nil_iff.mp hloc.symm)
    subst us
    rfl
  | cons i ts ih =>
    cases us with
    | nil => simp at hloc
    | cons j us =>
      obtain ⟨hij, htail⟩ := List.cons.inj hloc
      change x + position ω i = y + position η j at hij
      cases s with
      | none =>
        cases t with
        | some b => simp at hs
        | none =>
          by_cases hi : x + position ω i ∈ K
          · have hj : y + position η j ∈ K := by rw [← hij]; exact hi
            simpa only [scanChildIntervals, if_pos hi, if_pos hj] using
              ih us (some i) (some j) htail rfl
          · have hj : y + position η j ∉ K := by rw [← hij]; exact hi
            simpa only [scanChildIntervals, if_neg hi, if_neg hj] using
              ih us none none htail rfl
      | some a =>
        cases t with
        | none => simp at hs
        | some b =>
          by_cases hi : x + position ω i ∉ C
          · have hj : y + position η j ∉ C := by rw [← hij]; exact hi
            simpa only [scanChildIntervals, if_pos hi, if_pos hj, List.length_cons] using
              congrArg Nat.succ (ih us none none htail rfl)
          · have hj : ¬y + position η j ∉ C := by rw [← hij]; exact hi
            simpa only [scanChildIntervals, if_neg hi, if_neg hj] using
              ih us (some a) (some b) htail rfl

end SRWTightness
