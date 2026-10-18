import SRWTightness.CompletionResidualCount
import SRWTightness.ActualCompletionTimes
import SRWTightness.WordCompletionBoundary

namespace SRWTightness

/-- At either label's actual completion, the endpoint lies outside both child domains. -/
theorem actual_pair_completion_outside (D L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂)
    (hB : ∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂)
    (x : Site) (ω : Sample) (n : ℕ)
    (hn : n ∈ scanChildCompletionTimes L₁ C₁ x ω (domainSteps D x ω) ++
      scanChildCompletionTimes L₂ C₂ x ω (domainSteps D x ω)) :
    x + position ω n ∉ C₁ ∧ x + position ω n ∉ C₂ := by
  have hle : n ≤ domainSteps D x ω := by
    rcases List.mem_append.mp hn with h | h
    · exact scan_child_completion_time_le L₁ C₁ x ω _ n h
    · exact scan_child_completion_time_le L₂ C₂ x ω _ n h
  have hs : x + position ω n ∈
      wordMarkPairCompletionSites L₁ C₁ L₂ C₂ (some (x, killedPathWord D x ω)) := by
    rw [scan_child_completion_times_eq_killed_word,
      scan_child_completion_times_eq_killed_word] at hn
    change _ ∈ wordMarkCompletionSites L₁ C₁ _ ++ wordMarkCompletionSites L₂ C₂ _
    rw [← word_child_completion_times_sites, ← word_child_completion_times_sites]
    rw [← List.map_append]
    apply List.mem_map.mpr
    exact ⟨n, hn, congrArg (fun z ↦ x + z) (killedPathWord_position D x ω n hle)⟩
  exact (hB _ (word_mark_pair_completion_boundary L₁ C₁ L₂ C₂ hL₁ hL₂ _ _ hs)).2

/-- Later completions of both labels count exactly the two restarted killed child families. -/
theorem actual_pair_completion_residual_count (D L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂)
    (hB : ∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (n : ℕ)
    (hn : n ∈ scanChildCompletionTimes L₁ C₁ x ω (domainSteps D x ω) ++
      scanChildCompletionTimes L₂ C₂ x ω (domainSteps D x ω)) :
    (((scanChildCompletionTimes L₁ C₁ x ω (domainSteps D x ω) ++
      scanChildCompletionTimes L₂ C₂ x ω (domainSteps D x ω)).filter
        (fun k ↦ n < k)).length) =
      (killedChildIntervals D L₁ C₁ (x + position ω n) (shift n ω)).length +
        (killedChildIntervals D L₂ C₂ (x + position ω n) (shift n ω)).length := by
  have hle : n ≤ domainSteps D x ω := by
    rcases List.mem_append.mp hn with h | h
    · exact scan_child_completion_time_le L₁ C₁ x ω _ n h
    · exact scan_child_completion_time_le L₂ C₂ x ω _ n h
  obtain ⟨h₁, h₂⟩ := actual_pair_completion_outside D L₁ C₁ L₂ C₂ hL₁ hL₂ hB x ω n hn
  rw [List.filter_append, List.length_append,
    killed_child_completion_after_cut_length D L₁ C₁ hL₁ x ω hfin n hle h₁,
    killed_child_completion_after_cut_length D L₂ C₂ hL₂ x ω hfin n hle h₂]

end SRWTightness
