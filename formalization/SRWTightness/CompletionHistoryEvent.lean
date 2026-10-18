import SRWTightness.ChildCompletionPrefix

open MeasureTheory

namespace SRWTightness

/-- Survival through a deterministic time and completion there, observed from the finite prefix. -/
def childCompletionHistoryEvent (D L C : Finset Site) (x : Site) (n : ℕ) : Set Sample :=
  pathPrefixWord n ⁻¹' {w | (∀ i < n, x + position (wordPath w) i ∈ D) ∧
    n ∈ wordChildCompletionTimes L C x w}

/-- Completion together with parent survival is measurable in the history at that time. -/
theorem measurable_child_completion_history_event (D L C : Finset Site) (x : Site) (n : ℕ) :
    MeasurableSet[history n] (childCompletionHistoryEvent D L C x n) :=
  (Set.to_countable _).measurableSet.preimage (history_measurable_path_prefix_word n)

/-- The finite parent's exit horizon is determined by survival at all earlier positions. -/
theorem le_domain_steps_iff_prefix_survival (D : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) (n : ℕ) :
    n ≤ domainSteps D x ω ↔ ∀ i < n, x + position ω i ∈ D := by
  constructor
  · intro hn i hi
    exact position_before_domainSteps_mem D x ω hfin i (hi.trans_le hn)
  · intro h
    by_contra hn
    exact position_domain_exit_not_mem D x ω hfin (h _ (Nat.lt_of_not_ge hn))

/-- The actual full-parent completion event has a deterministic-history representation. -/
theorem scan_child_completion_history_iff (D L C : Finset Site) (hLC : L ⊆ C)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (n : ℕ) :
    n ∈ scanChildCompletionTimes L C x ω (domainSteps D x ω) ↔
      ω ∈ childCompletionHistoryEvent D L C x n := by
  rw [scan_child_completion_prefix_iff L C hLC,
    le_domain_steps_iff_prefix_survival D x ω hfin]
  change _ ↔ (∀ i < n, x + position (wordPath (pathPrefixWord n ω)) i ∈ D) ∧
    n ∈ wordChildCompletionTimes L C x (pathPrefixWord n ω)
  rw [word_child_times_prefix_eq_scan]
  apply and_congr _ Iff.rfl
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [path_prefix_word_position n ω i hi.le]

end SRWTightness
