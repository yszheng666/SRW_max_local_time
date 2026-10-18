import SRWTightness.ExteriorPathRecord

open MeasureTheory
namespace SRWTightness

/-- Every exterior header comes from one of the erased intervals, with the recorded label and endpoints. -/
theorem packExteriorRecord_slot (label : Site → Bool) (x : Site) (w : PathWord)
    (intervals : List (ℕ × ℕ)) (previous : ℕ) (s : ExteriorSlot)
    (hs : s ∈ (packExteriorRecord label x w previous intervals).1) :
    ∃ q ∈ intervals,
      s.2.1 = label (x + position (wordPath w) q.1) ∧
      s.2.2.1 = x + position (wordPath w) q.1 ∧
      s.2.2.2 = x + position (wordPath w) q.2 := by
  induction intervals generalizing previous with
  | nil => simp [packExteriorRecord] at hs
  | cons q qs ih =>
    rcases q with ⟨a, b⟩
    simp only [packExteriorRecord, List.mem_cons] at hs
    rcases hs with hs | hs
    · subst s
      exact ⟨(a, b), List.mem_cons_self, rfl, rfl, rfl⟩
    · obtain ⟨q, hq, hlabel, hstart, hend⟩ := ih b hs
      exact ⟨q, List.mem_cons_of_mem _ hq, hlabel, hstart, hend⟩

/-- Every actual exterior header starts in the inner target and exits the deleted domain. -/
theorem killedExteriorRecord_slot (D K C : Finset Site) (label : Site → Bool)
    (x : Site) (ω : Sample) (s : ExteriorSlot)
    (hs : s ∈ (killedExteriorRecord D K C label x ω).1) :
    s.2.2.1 ∈ K ∧ s.2.2.2 ∉ C ∧ s.2.1 = label s.2.2.1 := by
  obtain ⟨q, hq, hl, ha, hb⟩ := packExteriorRecord_slot label x (killedPathWord D x ω)
    _ 0 s hs
  have hp := wordChildIntervals_endpoints K C x (killedPathWord D x ω) q hq
  exact ⟨ha.symm ▸ hp.1, hb.symm ▸ hp.2, by rw [ha]; exact hl⟩

/-- Positive exterior atoms inherit the exact endpoint and label support of the actual path. -/
theorem exterior_atom_slot (D K C : Finset Site) (label : Site → Bool)
    (x : Site) (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D K C label x ω = h})
    (s : ExteriorSlot) (hs : s ∈ h.1) :
    s.2.2.1 ∈ K ∧ s.2.2.2 ∉ C ∧ s.2.1 = label s.2.2.1 := by
  obtain ⟨ω, hω⟩ := nonempty_of_measureReal_ne_zero hh.ne'
  have hslot : s ∈ (killedExteriorRecord D K C label x ω).1 := by
    rw [show killedExteriorRecord D K C label x ω = h from hω]
    exact hs
  exact killedExteriorRecord_slot D K C label x ω s hslot

end SRWTightness
