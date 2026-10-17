import SRWTightness.CompletionHistoryEvent

open MeasureTheory

namespace SRWTightness

/-- Either label's completion with parent survival, observed at the common deterministic time. -/
def pairCompletionHistoryEvent (D L₁ C₁ L₂ C₂ : Finset Site) (x : Site) (n : ℕ) : Set Sample :=
  childCompletionHistoryEvent D L₁ C₁ x n ∪ childCompletionHistoryEvent D L₂ C₂ x n

/-- The two-label completion event depends only on the already observed increments. -/
theorem measurable_pair_completion_history_event (D L₁ C₁ L₂ C₂ : Finset Site)
    (x : Site) (n : ℕ) : MeasurableSet[history n]
      (pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n) :=
  (measurable_child_completion_history_event D L₁ C₁ x n).union
    (measurable_child_completion_history_event D L₂ C₂ x n)

/-- The actual restart position is measurable in its deterministic past. -/
theorem history_measurable_restart_site (x : Site) (n : ℕ) :
    Measurable[history n] (fun ω ↦ x + position ω n) :=
  (measurable_of_countable (fun z : Site ↦ x + z)).comp (adapted_position n)

/-- Actual two-label completion is exactly the corresponding past event before finite exit. -/
theorem actual_pair_completion_history_iff (D L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) (n : ℕ) :
    n ∈ scanChildCompletionTimes L₁ C₁ x ω (domainSteps D x ω) ++
      scanChildCompletionTimes L₂ C₂ x ω (domainSteps D x ω) ↔
    ω ∈ pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n := by
  rw [List.mem_append, scan_child_completion_history_iff D L₁ C₁ hL₁ x ω hfin n,
    scan_child_completion_history_iff D L₂ C₂ hL₂ x ω hfin n]
  rfl

end SRWTightness
