import SRWTightness.ExteriorPathRecord
import SRWTightness.PathWordNestedSlice

namespace SRWTightness

/-- Repacking a suffix translates every recorded time while preserving all exterior words and sites.
-/
theorem packExteriorRecord_suffix_shift (label : Site → Bool) (x : Site) (w : PathWord)
    (b previous : ℕ) (hb : b ≤ w.length) (hp : previous ≤ w.length - b)
    (intervals : List (ℕ × ℕ))
    (horder : intervals.Pairwise (fun q r ↦ q.2 < r.1))
    (hbound : ∀ q ∈ intervals, previous ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ w.length - b) :
    packExteriorRecord label (x + position (wordPath w) b)
      (slicePathWord w b w.length) previous intervals =
    packExteriorRecord label x w (b + previous)
      (intervals.map (fun q ↦ (b + q.1, b + q.2))) := by
  have hpos (i : ℕ) (hi : i ≤ w.length - b) :
      (x + position (wordPath w) b) +
        position (wordPath (slicePathWord w b w.length)) i =
          x + position (wordPath w) (b + i) := by
    rw [slicePathWord_position w b w.length i hi, add_assoc, ← position_add]
  induction intervals generalizing previous with
  | nil =>
    simp only [packExteriorRecord, List.map_nil]
    change ([], slicePathWord (slicePathWord w b w.length) previous (w.length - b)) = _
    rw [slicePathWord_nested w b w.length previous (w.length - b) hp le_rfl]
    have he : b + (w.length - b) = w.length := by omega
    rw [he]
  | cons q intervals ih =>
    rcases q with ⟨a, c⟩
    obtain ⟨hbefore, horderTail⟩ := List.pairwise_cons.mp horder
    obtain ⟨hpa, hac, hc⟩ := hbound (a, c) List.mem_cons_self
    have htail := ih c hc horderTail (by
      intro r hr
      obtain ⟨_, hrlt, hrN⟩ := hbound r (List.mem_cons_of_mem (a, c) hr)
      exact ⟨(hbefore r hr).le, hrlt, hrN⟩)
    simp only [packExteriorRecord, List.map_cons, htail,
      slicePathWord_nested w b w.length previous a hpa (hac.trans hc),
      hpos a (hac.trans hc), hpos c hc]

end SRWTightness
