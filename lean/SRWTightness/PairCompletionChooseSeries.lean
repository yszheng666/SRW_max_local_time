import SRWTightness.PairCompletionBinomialIdentity
import SRWTightness.PairCompletionHistory
import SRWTightness.CompletionListTsum
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped ENNReal

namespace SRWTightness

/-- Positive-order factorial counts are the nonnegative series of future completion rewards. -/
theorem actual_pair_choose_eq_future_series (D L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (hC : Disjoint C₁ C₂)
    (hB : ∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (p : ℕ) :
    ((wordMarkRootCount L₁ C₁ (killedWordMark D x ω) +
      wordMarkRootCount L₂ C₂ (killedWordMark D x ω)).choose (p + 1) : ℝ≥0∞) =
    ∑' n, (pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n).indicator
      (fun υ ↦ ((wordMarkRootCount L₁ C₁
        (killedWordMark D (x + position υ n) (shift n υ)) + wordMarkRootCount L₂ C₂
          (killedWordMark D (x + position υ n) (shift n υ))).choose p : ℝ≥0∞)) ω := by
  classical
  let ts := scanChildCompletionTimes L₁ C₁ x ω (domainSteps D x ω) ++
    scanChildCompletionTimes L₂ C₂ x ω (domainSteps D x ω)
  have ht : ts.Nodup :=
    disjoint_actual_pair_completion_times_nodup D L₁ C₁ L₂ C₂ hL₁ hL₂ hC x ω
  have h := congrArg (fun v : ℕ ↦ (v : ℝ≥0∞))
    (actual_pair_completion_choose_identity D L₁ C₁ L₂ C₂ hL₁ hL₂ hC hB x ω hfin p)
  rw [Nat.cast_list_sum, List.map_map] at h
  change _ = (ts.map _).sum at h
  rw [completion_list_sum_eq_tsum ts ht] at h
  change _ = _ at h
  change _ = _
  convert h using 1
  · rfl
  · apply tsum_congr
    intro n
    rw [Set.indicator_apply]
    have he := actual_pair_completion_history_iff D L₁ C₁ L₂ C₂ hL₁ hL₂ x ω hfin n
    change (if ω ∈ pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n then _ else 0) =
      (if n ∈ ts then _ else 0)
    rw [← he]
    by_cases hn : n ∈ ts <;>
      simp [ts, wordMarkRootCount, killedWordMark, killedChildIntervals, hn] at *

end SRWTightness
