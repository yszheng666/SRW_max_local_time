import SRWTightness.VisitTraceRange
import SRWTightness.PathPrefixWord
import SRWTightness.CompletionHistoryEvent

open MeasureTheory

namespace SRWTightness

/-- The history ending with a specified chronological trace at time n, before killing. -/
def visitTraceHistoryEvent (D K : Finset Site) (x : Site) (ξ : List Site)
    (n : ℕ) : Set Sample :=
  pathPrefixWord n ⁻¹' {w | (∀ i ≤ n, x + position (wordPath w) i ∈ D) ∧
    x + position (wordPath w) n ∈ K ∧
    wordVisitTrace K x w ++ [x + position (wordPath w) n] = ξ}

/-- The endpoint trace event depends only on increments before its deterministic time. -/
theorem measurable_visit_trace_history_event (D K : Finset Site) (x : Site)
    (ξ : List Site) (n : ℕ) :
    MeasurableSet[history n] (visitTraceHistoryEvent D K x ξ n) :=
  (Set.to_countable _).measurableSet.preimage (history_measurable_path_prefix_word n)

/-- The prefix-word history event agrees with the original path positions and visits. -/
theorem visit_trace_history_event_iff (D K : Finset Site) (x : Site)
    (ξ : List Site) (n : ℕ) (ω : Sample) :
    ω ∈ visitTraceHistoryEvent D K x ξ n ↔
      (∀ i ≤ n, x + position ω i ∈ D) ∧ x + position ω n ∈ K ∧
      visitTraceRange K x ω n ++ [x + position ω n] = ξ := by
  change ((∀ i ≤ n, x + position (wordPath (pathPrefixWord n ω)) i ∈ D) ∧ _) ↔ _
  rw [word_visit_trace_eq_range]
  have he : visitTraceRange K x (wordPath (pathPrefixWord n ω)) n =
      visitTraceRange K x ω n :=
    visit_trace_range_congr K x _ _ n (fun i hi ↦ path_prefix_word_position n ω i hi.le)
  change ((∀ i ≤ n, x + position (wordPath (pathPrefixWord n ω)) i ∈ D) ∧
    x + position (wordPath (pathPrefixWord n ω)) n ∈ K ∧
    visitTraceRange K x (wordPath (pathPrefixWord n ω)) n ++
      [x + position (wordPath (pathPrefixWord n ω)) n] = ξ) ↔ _
  rw [he, path_prefix_word_position n ω n le_rfl]
  apply and_congr _ Iff.rfl
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [path_prefix_word_position n ω i hi]

/-- A history event fixes the restart site to the final entry of its trace. -/
theorem visit_trace_history_last (D K : Finset Site) (x : Site)
    (ξ : List Site) (n : ℕ) (ω : Sample)
    (h : ω ∈ visitTraceHistoryEvent D K x ξ n) :
    x + position ω n = ξ.getLastD x := by
  have he := (visit_trace_history_event_iff D K x ξ n ω).mp h
  rw [← he.2.2, List.getLastD_concat]

/-- The endpoint of a history event is strictly before the finite parent exit. -/
theorem visit_trace_history_before_exit (D K : Finset Site) (x : Site)
    (ξ : List Site) (n : ℕ) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤)
    (h : ω ∈ visitTraceHistoryEvent D K x ξ n) : n < domainSteps D x ω := by
  have he := (visit_trace_history_event_iff D K x ξ n ω).mp h
  have hn : n + 1 ≤ domainSteps D x ω :=
    (le_domain_steps_iff_prefix_survival D x ω hfin (n + 1)).mpr
      (fun i hi ↦ he.1 i (by omega))
  omega

/-- At a history endpoint the chronological trace through that endpoint is prescribed. -/
theorem visit_trace_history_range (D K : Finset Site) (x : Site)
    (ξ : List Site) (n : ℕ) (ω : Sample)
    (h : ω ∈ visitTraceHistoryEvent D K x ξ n) :
    visitTraceRange K x ω (n + 1) = ξ := by
  have he := (visit_trace_history_event_iff D K x ξ n ω).mp h
  rw [visit_trace_range_succ, if_pos he.2.1]
  exact he.2.2

/-- Traces through increasing deterministic horizons have nondecreasing lengths. -/
theorem visit_trace_range_length_mono (K : Finset Site) (x : Site) (ω : Sample)
    {n m : ℕ} (h : n ≤ m) :
    (visitTraceRange K x ω n).length ≤ (visitTraceRange K x ω m).length := by
  have he := visit_trace_range_add K x ω n (m - n)
  rw [Nat.add_sub_of_le h] at he
  have hlen := congrArg List.length he
  rw [List.length_append] at hlen
  omega

/-- A prescribed trace can finish at only one history time, even with repeated sites. -/
theorem visit_trace_history_pairwise_disjoint (D K : Finset Site) (x : Site)
    (ξ : List Site) : Pairwise (fun n m ↦ Disjoint (visitTraceHistoryEvent D K x ξ n)
      (visitTraceHistoryEvent D K x ξ m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro ω hn hm
  have distinct_order (a b : ℕ) (hab : a < b)
      (ha : ω ∈ visitTraceHistoryEvent D K x ξ a)
      (hb : ω ∈ visitTraceHistoryEvent D K x ξ b) : False := by
    have hle := visit_trace_range_length_mono K x ω (Nat.succ_le_of_lt hab)
    have hpa := visit_trace_history_range D K x ξ a ω ha
    have hpb := (visit_trace_history_event_iff D K x ξ b ω).mp hb
    have hlen := congrArg List.length hpb.2.2
    rw [List.length_append, List.length_singleton] at hlen
    rw [hpa] at hle
    omega
  rcases lt_or_gt_of_ne hnm with h | h
  · exact distinct_order n m h hn hm
  · exact distinct_order m n h hm hn

end SRWTightness
