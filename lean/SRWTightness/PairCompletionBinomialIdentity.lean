import SRWTightness.PairCompletionResidual
import SRWTightness.ListOrderedBinomialSum

namespace SRWTightness

/-- Each positive-order subset is assigned to its first completion, then counted in the future. -/
theorem actual_pair_completion_choose_identity (D L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (hC : Disjoint C₁ C₂)
    (hB : ∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (p : ℕ) :
    (((killedChildIntervals D L₁ C₁ x ω).length +
      (killedChildIntervals D L₂ C₂ x ω).length).choose (p + 1)) =
    ((scanChildCompletionTimes L₁ C₁ x ω (domainSteps D x ω) ++
      scanChildCompletionTimes L₂ C₂ x ω (domainSteps D x ω)).map
        (fun n ↦ (((killedChildIntervals D L₁ C₁
          (x + position ω n) (shift n ω)).length +
          (killedChildIntervals D L₂ C₂ (x + position ω n)
            (shift n ω)).length).choose p))).sum := by
  let ts := scanChildCompletionTimes L₁ C₁ x ω (domainSteps D x ω) ++
    scanChildCompletionTimes L₂ C₂ x ω (domainSteps D x ω)
  have ht : ts.Nodup :=
    disjoint_actual_pair_completion_times_nodup D L₁ C₁ L₂ C₂ hL₁ hL₂ hC x ω
  have hlen : ts.length = (killedChildIntervals D L₁ C₁ x ω).length +
      (killedChildIntervals D L₂ C₂ x ω).length := by
    simp only [ts, List.length_append, actual_completion_times_length]
  rw [← hlen, ← list_sum_choose_later_length ts ht p]
  apply congrArg List.sum
  apply List.map_congr_left
  intro n hn
  rw [actual_pair_completion_residual_count D L₁ C₁ L₂ C₂ hL₁ hL₂ hB x ω hfin n hn]

end SRWTightness
