import SRWTightness.WordCompletionBoundary
import SRWTightness.ChildIntervalSeparation

namespace SRWTightness

/-- Completion times retain every chronological child, including repeated exit positions. -/
def wordChildCompletionTimes (L C : Finset Site) (x : Site) (w : PathWord) : List ℕ :=
  (wordChildIntervals L C x w).map Prod.snd

/-- Immediately before a complete child exits, its actual position still lies in its domain. -/
theorem word_child_completion_predecessor_inside (L C : Finset Site) (hLC : L ⊆ C)
    (x : Site) (w : PathWord) (q : ℕ × ℕ) (hq : q ∈ wordChildIntervals L C x w) :
    x + position (wordPath w) (q.2 - 1) ∈ C := by
  have hlt : q.1 < q.2 := scanChildIntervals_start_lt_end L C x (wordPath w) _
    List.pairwise_lt_range none (by intro a h; cases h) q hq
  exact wordChildIntervals_interior L C hLC x w q hq _ (by omega) (by omega)

/-- Children in disjoint domains cannot complete at the same actual time. -/
theorem disjoint_word_child_completion_times (L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (hC : Disjoint C₁ C₂)
    (x : Site) (w : PathWord) (q₁ q₂ : ℕ × ℕ)
    (hq₁ : q₁ ∈ wordChildIntervals L₁ C₁ x w)
    (hq₂ : q₂ ∈ wordChildIntervals L₂ C₂ x w) : q₁.2 ≠ q₂.2 := by
  intro he
  have h₁ := word_child_completion_predecessor_inside L₁ C₁ hL₁ x w q₁ hq₁
  have h₂ := word_child_completion_predecessor_inside L₂ C₂ hL₂ x w q₂ hq₂
  rw [← he] at h₂
  exact Finset.disjoint_left.mp hC h₁ h₂

/-- The completion times of each label are strictly increasing. -/
theorem word_child_completion_times_strict (L C : Finset Site) (x : Site) (w : PathWord) :
    (wordChildCompletionTimes L C x w).Pairwise (· < ·) := by
  unfold wordChildCompletionTimes
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem ?_
    (scanChildIntervals_separated L C x (wordPath w) _ List.pairwise_lt_range none)
  intro a b ha hb hab
  have hlt := scanChildIntervals_start_lt_end L C x (wordPath w) _
    List.pairwise_lt_range none (by intro c h; cases h) b hb
  exact hab.trans hlt

/-- Completion times of one label have no repetitions. -/
theorem word_child_completion_times_nodup (L C : Finset Site) (x : Site) (w : PathWord) :
    (wordChildCompletionTimes L C x w).Nodup :=
  List.nodup_iff_pairwise_ne.mpr
    ((word_child_completion_times_strict L C x w).imp (fun h ↦ Nat.ne_of_lt h))

/-- Appending disjoint labels' completion times keeps every root and has no duplicate time. -/
theorem disjoint_word_pair_completion_times_nodup (L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (hC : Disjoint C₁ C₂) (x : Site) (w : PathWord) :
    (wordChildCompletionTimes L₁ C₁ x w ++ wordChildCompletionTimes L₂ C₂ x w).Nodup := by
  rw [List.nodup_append]
  refine ⟨word_child_completion_times_nodup _ _ _ _,
    word_child_completion_times_nodup _ _ _ _, ?_⟩
  intro a ha b hb
  obtain ⟨q₁, hq₁, rfl⟩ := List.mem_map.mp ha
  obtain ⟨q₂, hq₂, rfl⟩ := List.mem_map.mp hb
  exact disjoint_word_child_completion_times L₁ C₁ L₂ C₂ hL₁ hL₂ hC x w q₁ q₂ hq₁ hq₂

/-- Mapping completion times back to actual positions is exactly the original completion list. -/
theorem word_child_completion_times_sites (L C : Finset Site) (x : Site) (w : PathWord) :
    (wordChildCompletionTimes L C x w).map (fun n ↦ x + position (wordPath w) n) =
      wordMarkCompletionSites L C (some (x, w)) := by
  simp [wordChildCompletionTimes, wordMarkCompletionSites, List.map_map]

end SRWTightness
