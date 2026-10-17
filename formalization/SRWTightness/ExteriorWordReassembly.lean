import SRWTightness.PathWordDirectionsSlice
import SRWTightness.ExteriorPathRecord
import SRWTightness.ChildIntervalSeparation

namespace SRWTightness

/-- Reinsert a chronological list of internal words between the retained exterior pieces. -/
def reassembleExteriorWord : ExteriorPathRecord → List PathWord → PathWord
  | ([], tail), _ => tail
  | (slot :: slots, tail), [] => pathWordAppend slot.1 (reassembleExteriorWord (slots, tail) [])
  | (slot :: slots, tail), u :: us =>
      pathWordAppend slot.1 (pathWordAppend u (reassembleExteriorWord (slots, tail) us))

/-- Reassembling the slices of an ordered interval list recovers the original remaining word. -/
theorem reassembleExteriorWord_pack (label : Site → Bool) (x : Site) (w : PathWord)
    (intervals : List (ℕ × ℕ)) (previous : ℕ)
    (horder : intervals.Pairwise (fun q r ↦ q.2 < r.1))
    (hbound : ∀ q ∈ intervals, previous ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ w.length) :
    reassembleExteriorWord (packExteriorRecord label x w previous intervals)
      (intervals.map (fun q ↦ slicePathWord w q.1 q.2)) =
        slicePathWord w previous w.length := by
  induction intervals generalizing previous with
  | nil => simp [reassembleExteriorWord, packExteriorRecord]
  | cons q intervals ih =>
    rcases q with ⟨a, b⟩
    obtain ⟨hbefore, horderTail⟩ := List.pairwise_cons.mp horder
    obtain ⟨hp, hab, hb⟩ := hbound (a, b) List.mem_cons_self
    simp only [packExteriorRecord, List.map_cons, reassembleExteriorWord]
    rw [ih b horderTail (by
      intro r hr
      obtain ⟨_, hrlt, hrN⟩ := hbound r (List.mem_cons_of_mem (a, b) hr)
      exact ⟨(hbefore r hr).le, hrlt, hrN⟩)]
    rw [pathWordAppend_slices w a b w.length hab hb le_rfl,
      pathWordAppend_slices w previous a w.length hp (hab.trans hb) le_rfl]

/-- The actual exterior record and complete internal words together determine the entire word. -/
theorem reassembleExteriorWord_actual (K C : Finset Site) (label : Site → Bool)
    (x : Site) (w : PathWord) :
    reassembleExteriorWord (wordExteriorRecord K C label x w)
      (wordChildRecords K C x (fun _ u ↦ u) w) = w := by
  rw [wordExteriorRecord, wordChildRecords]
  have hh := reassembleExteriorWord_pack label x w (wordChildIntervals K C x w) 0
    (scanChildIntervals_separated K C x (wordPath w) _ List.pairwise_lt_range none)
    (by
      intro q hq
      have ht := wordChildIntervals_endpoint_le K C x w q hq
      have ho := scanChildIntervals_start_lt_end K C x (wordPath w) _
        List.pairwise_lt_range none (by intro a he; cases he) q hq
      exact ⟨Nat.zero_le _, ho.le, ht.2⟩)
  exact hh.trans (slicePathWord_full w)

end SRWTightness
