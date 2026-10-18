import SRWTightness.ChildCompletionPrefix

namespace SRWTightness

/-- Actual scan completion times retain exactly the killed word's interval endpoints. -/
theorem scan_child_completion_times_eq_killed_word (D L C : Finset Site)
    (x : Site) (ω : Sample) :
    scanChildCompletionTimes L C x ω (domainSteps D x ω) =
      wordChildCompletionTimes L C x (killedPathWord D x ω) := by
  change _ = (killedChildIntervals D L C x ω).map Prod.snd
  rw [killedChildIntervals_eq_scan]
  rfl

/-- Disjoint labels' actual completion times have no repetitions. -/
theorem disjoint_actual_pair_completion_times_nodup (D L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (hC : Disjoint C₁ C₂) (x : Site) (ω : Sample) :
    (scanChildCompletionTimes L₁ C₁ x ω (domainSteps D x ω) ++
      scanChildCompletionTimes L₂ C₂ x ω (domainSteps D x ω)).Nodup := by
  rw [scan_child_completion_times_eq_killed_word, scan_child_completion_times_eq_killed_word]
  exact disjoint_word_pair_completion_times_nodup L₁ C₁ L₂ C₂ hL₁ hL₂ hC x _

/-- The actual completion list has one time per child interval. -/
theorem actual_completion_times_length (D L C : Finset Site) (x : Site) (ω : Sample) :
    (scanChildCompletionTimes L C x ω (domainSteps D x ω)).length =
      (killedChildIntervals D L C x ω).length := by
  rw [scan_child_completion_times_eq_killed_word]
  simp only [wordChildCompletionTimes, List.length_map, killedChildIntervals]

end SRWTightness
