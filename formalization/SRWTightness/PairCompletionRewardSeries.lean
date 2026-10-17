import SRWTightness.PairCompletionHistory
import SRWTightness.ActualCompletionTimes
import SRWTightness.CompletionListTsum
import SRWTightness.WordCompletionSites

open scoped ENNReal

namespace SRWTightness

/-- Actual completion-site rewards preserve the ordered list and its repeated spatial sites. -/
theorem actual_pair_completion_reward_times (D L₁ C₁ L₂ C₂ : Finset Site)
    (x : Site) (ω : Sample) (f : Site → ℝ≥0∞) :
    ((wordMarkPairCompletionSites L₁ C₁ L₂ C₂ (killedWordMark D x ω)).map f).sum =
      ((scanChildCompletionTimes L₁ C₁ x ω (domainSteps D x ω) ++
        scanChildCompletionTimes L₂ C₂ x ω (domainSteps D x ω)).map
          (fun n ↦ f (x + position ω n))).sum := by
  change ((wordMarkCompletionSites L₁ C₁ (some (x, killedPathWord D x ω)) ++
    wordMarkCompletionSites L₂ C₂ (some (x, killedPathWord D x ω))).map f).sum = _
  rw [← word_child_completion_times_sites, ← word_child_completion_times_sites,
    ← List.map_append, List.map_map, ← scan_child_completion_times_eq_killed_word,
    ← scan_child_completion_times_eq_killed_word]
  apply congrArg List.sum
  apply List.map_congr_left
  intro n hn
  have hle : n ≤ domainSteps D x ω := by
    rcases List.mem_append.mp hn with h | h
    · exact scan_child_completion_time_le L₁ C₁ x ω _ n h
    · exact scan_child_completion_time_le L₂ C₂ x ω _ n h
  simp only [Function.comp_apply, killedPathWord_position D x ω n hle]

/-- Completion rewards form a deterministic-time indicator series on the parent law. -/
theorem actual_pair_completion_reward_series (D L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (hC : Disjoint C₁ C₂)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (f : Site → ℝ≥0∞) :
    ((wordMarkPairCompletionSites L₁ C₁ L₂ C₂ (killedWordMark D x ω)).map f).sum =
      ∑' n, (pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n).indicator
        (fun υ ↦ f (x + position υ n)) ω := by
  classical
  rw [actual_pair_completion_reward_times,
    completion_list_sum_eq_tsum _
      (disjoint_actual_pair_completion_times_nodup D L₁ C₁ L₂ C₂ hL₁ hL₂ hC x ω)]
  apply tsum_congr
  intro n
  rw [Set.indicator_apply,
    ← actual_pair_completion_history_iff D L₁ C₁ L₂ C₂ hL₁ hL₂ x ω hfin n]
  by_cases hn : n ∈ scanChildCompletionTimes L₁ C₁ x ω (domainSteps D x ω) ++
    scanChildCompletionTimes L₂ C₂ x ω (domainSteps D x ω) <;> simp [hn]

end SRWTightness
