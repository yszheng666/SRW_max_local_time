import SRWTightness.ActualChildRecords

namespace SRWTightness

/-- A zero-length direction word cannot contain a complete child interval. -/
theorem wordChildRecords_zero_length {M : Type*} (K C : Finset Site) (x : Site)
    (F : Site → PathWord → M) (w : PathWord) (hw : w.length = 0) :
    wordChildRecords K C x F w = [] := by
  simp only [wordChildRecords, wordChildIntervals, hw, Nat.zero_add, List.range_one]
  simp only [scanChildIntervals]
  split_ifs <;> rfl

/-- Without any entrance observation, a finite word has no complete child records. -/
theorem wordChildRecords_no_visit {M : Type*} (K C : Finset Site) (x : Site)
    (F : Site → PathWord → M) (w : PathWord)
    (hvisit : ∀ i ≤ w.length, x + position (wordPath w) i ∉ K) :
    wordChildRecords K C x F w = [] := by
  have hh := scanChildIntervals_skip_prefix K C x (wordPath w)
    (List.range (w.length + 1)) []
    (fun i hi ↦ hvisit i (by simpa using List.mem_range.mp hi))
  simpa only [List.append_nil, scanChildIntervals, wordChildRecords, wordChildIntervals,
    List.map_nil] using congrArg
      (List.map (fun q ↦ F (x + position (wordPath w) q.1) (slicePathWord w q.1 q.2))) hh

end SRWTightness
