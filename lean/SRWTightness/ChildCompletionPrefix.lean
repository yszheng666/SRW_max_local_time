import SRWTightness.ChildCountBoundarySplit
import SRWTightness.WordCompletionTimes
import SRWTightness.PathPrefixWord

namespace SRWTightness

/-- Completion times emitted through an included deterministic horizon. -/
def scanChildCompletionTimes (L C : Finset Site) (x : Site) (ω : Sample) (N : ℕ) : List ℕ :=
  (scanChildIntervals L C x ω none (List.range (N + 1))).map Prod.snd

/-- The recorded deterministic prefix has exactly the actual scan's completion times. -/
theorem word_child_times_prefix_eq_scan (L C : Finset Site) (x : Site) (n : ℕ) (ω : Sample) :
    wordChildCompletionTimes L C x (pathPrefixWord n ω) = scanChildCompletionTimes L C x ω n := by
  unfold wordChildCompletionTimes wordChildIntervals scanChildCompletionTimes
  change (scanChildIntervals L C x (wordPath (pathPrefixWord n ω)) none
    (List.range (n + 1))).map Prod.snd = _
  congr 1
  apply scanChildIntervals_position_congr
  intro i hi
  exact path_prefix_word_position n ω i (by have hh := List.mem_range.mp hi; omega)

/-- An emitted completion never occurs after the inspected horizon. -/
theorem scan_child_completion_time_le (L C : Finset Site) (x : Site) (ω : Sample) (N n : ℕ)
    (hn : n ∈ scanChildCompletionTimes L C x ω N) : n ≤ N := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hn
  have ht := (scanChildIntervals_endpoint_times L C x ω _ none q hq).2
  have hh := List.mem_range.mp ht
  omega

/-- A completion's actual endpoint is outside its own child domain. -/
theorem scan_child_completion_outside (L C : Finset Site) (x : Site) (ω : Sample) (N n : ℕ)
    (hn : n ∈ scanChildCompletionTimes L C x ω N) : x + position ω n ∉ C := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hn
  exact (scanChildIntervals_endpoints L C x ω _ none (by intro a h; cases h) q hq).2

/-- Later scanning cannot add or remove a completion at an already inspected outside point. -/
theorem scan_child_completion_at_cut (L C : Finset Site) (hLC : L ⊆ C)
    (x : Site) (ω : Sample) (n N : ℕ) (hn : n ≤ N) (hout : x + position ω n ∉ C) :
    n ∈ scanChildCompletionTimes L C x ω N ↔ n ∈ scanChildCompletionTimes L C x ω n := by
  let tail := scanChildIntervals L C (x + position ω n) (shift n ω) none
    (List.range (N - n + 1))
  have hf : n ∉ tail.map (fun q ↦ n + q.2) := by
    intro h
    obtain ⟨q, hq, he⟩ := List.mem_map.mp h
    have hpos := scanChildIntervals_start_lt_end L C (x + position ω n) (shift n ω) _
      List.pairwise_lt_range none (by intro a h; cases h) q hq
    omega
  have hm : (tail.map (fun q ↦ (n + q.1, n + q.2))).map Prod.snd =
      tail.map (fun q ↦ n + q.2) := by rw [List.map_map]; rfl
  unfold scanChildCompletionTimes
  rw [scan_child_intervals_boundary_split L C hLC x ω n N hn hout, List.map_append]
  change n ∈ (scanChildIntervals L C x ω none (List.range (n + 1))).map Prod.snd ++
    (tail.map (fun q ↦ (n + q.1, n + q.2))).map Prod.snd ↔ _
  rw [hm]
  simp only [List.mem_append, hf, or_false]

/-- Completion at a full horizon is exactly survival through that time and prefix completion. -/
theorem scan_child_completion_prefix_iff (L C : Finset Site) (hLC : L ⊆ C)
    (x : Site) (ω : Sample) (N n : ℕ) :
    n ∈ scanChildCompletionTimes L C x ω N ↔
      n ≤ N ∧ n ∈ scanChildCompletionTimes L C x ω n := by
  constructor
  · intro h
    have hn := scan_child_completion_time_le L C x ω N n h
    have hout := scan_child_completion_outside L C x ω N n h
    exact ⟨hn, (scan_child_completion_at_cut L C hLC x ω n N hn hout).mp h⟩
  · rintro ⟨hn, h⟩
    have hout := scan_child_completion_outside L C x ω n n h
    exact (scan_child_completion_at_cut L C hLC x ω n N hn hout).mpr h

end SRWTightness
