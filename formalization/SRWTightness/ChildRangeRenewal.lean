import SRWTightness.ChildScanRenewal

namespace SRWTightness

/-- Split the full observation range at an entrance and a later exit. -/
theorem child_time_range_split (a b N : ℕ) (hab : a < b) (hb : b ≤ N) :
    List.range (N + 1) = List.range a ++
      a :: (List.range' (a + 1) (b - a - 1) ++ b :: List.range' (b + 1) (N - b)) := by
  have hm : a + 1 + (b - a - 1) = b := by omega
  have hn : b - a - 1 + (N - b + 1) = N - a := by omega
  have ht : a + (N - a + 1) = N + 1 := by omega
  have hs := List.range'_append_1 (s := a + 1) (m := b - a - 1)
    (n := N - b + 1)
  rw [hm, hn, List.range'_succ] at hs
  rw [hs]
  rw [← List.range'_succ, List.range_eq_range', List.range_eq_range']
  simpa only [Nat.zero_add, ht] using
    (List.range'_append_1 (s := 0) (m := a) (n := N - a + 1)).symm

/-- A complete range scan renews on the shifted walk immediately after the first exit. -/
theorem scanChildIntervals_range_restart (K C : Finset Site) (x : Site) (ω : Sample)
    (a b N : ℕ) (hab : a < b) (hb : b ≤ N)
    (hpre : ∀ i < a, x + position ω i ∉ K) (ha : x + position ω a ∈ K)
    (hin : ∀ i, a < i → i < b → x + position ω i ∈ C)
    (hout : x + position ω b ∉ C) :
    scanChildIntervals K C x ω none (List.range (N + 1)) =
      (a, b) :: (scanChildIntervals K C (x + position ω (b + 1))
        (shift (b + 1) ω) none (List.range (N - b))).map
          (fun q ↦ (b + 1 + q.1, b + 1 + q.2)) := by
  rw [child_time_range_split a b N hab hb]
  rw [scanChildIntervals_first_child_restart K C x ω a b]
  · congr 1
    rw [List.range'_eq_map_range]
    exact scanChildIntervals_shift K C x ω (b + 1) (List.range (N - b)) none
  · intro i hi
    exact hpre i (List.mem_range.mp hi)
  · exact ha
  · intro i hi
    have hh := List.mem_range'.mp hi
    obtain ⟨k, hk, he⟩ := hh
    simp only [Nat.one_mul] at he
    apply hin i <;> omega
  · exact hout

end SRWTightness
