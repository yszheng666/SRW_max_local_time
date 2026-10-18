import SRWTightness.FiniteRootCompletionInput
import SRWTightness.PairCompletionChooseSeries
import SRWTightness.PairCompletionMomentSeries
import SRWTightness.PairCompletionRewardSeries

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Integrating actual completion rewards gives the series of deterministic-time restart rewards. -/
theorem killed_pair_completion_reward_integral_series (D L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (hC : Disjoint C₁ C₂)
    (x : Site) (f : Site → ℝ≥0∞) :
    (∫⁻ Y, ((wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y).map f).sum ∂killedWordMarkLaw D x) =
      ∑' n, ∫⁻ ω, f (x + position ω n)
        ∂pathLaw.restrict (pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n) := by
  unfold killedWordMarkLaw
  rw [lintegral_map (measurable_of_countable _) (measurable_killedWordMark D x)]
  calc
    _ = ∫⁻ ω, ∑' n, (pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n).indicator
        (fun υ ↦ f (x + position υ n)) ω ∂pathLaw := by
      apply lintegral_congr_ae
      filter_upwards [domainExit_ne_top_ae D x] with ω hfin
      exact actual_pair_completion_reward_series D L₁ C₁ L₂ C₂ hL₁ hL₂ hC x ω hfin f
    _ = _ := by
      have hE (n : ℕ) : MeasurableSet (pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n) :=
        (history.le n) _ (measurable_pair_completion_history_event D L₁ C₁ L₂ C₂ x n)
      have hf (n : ℕ) : Measurable (fun ω ↦ f (x + position ω n)) :=
        (measurable_of_countable f).comp
          ((history_measurable_restart_site x n).mono (history.le n) le_rfl)
      rw [lintegral_tsum (fun n ↦ ((hf n).indicator (hE n)).aemeasurable)]
      apply tsum_congr
      intro n
      exact lintegral_indicator (hE n) _

/-- All-order factorial recurrence follows from actual completion times and future steps. -/
theorem killed_root_binomial_recurrence_internal (D L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂) (hC : Disjoint C₁ C₂)
    (hB : ∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂)
    (x : Site) (p : ℕ) :
    killedRootBinomialMoment D L₁ C₁ L₂ C₂ x (p + 1) =
      ∫⁻ Y, ((wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y).map
        (fun z ↦ killedRootBinomialMoment D L₁ C₁ L₂ C₂ z p)).sum ∂killedWordMarkLaw D x := by
  rw [killed_root_binomial_moment_path_integral]
  calc
    _ = ∫⁻ ω, ∑' n, (pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n).indicator
        (fun υ ↦ ((wordMarkRootCount L₁ C₁
          (killedWordMark D (x + position υ n) (shift n υ)) + wordMarkRootCount L₂ C₂
            (killedWordMark D (x + position υ n) (shift n υ))).choose p : ℝ≥0∞)) ω ∂pathLaw := by
      apply lintegral_congr_ae
      filter_upwards [domainExit_ne_top_ae D x] with ω hfin
      exact actual_pair_choose_eq_future_series D L₁ C₁ L₂ C₂ hL₁ hL₂ hC hB x ω hfin p
    _ = _ := (pair_completion_future_moment_series D L₁ C₁ L₂ C₂ x p).trans
      (killed_pair_completion_reward_integral_series D L₁ C₁ L₂ C₂ hL₁ hL₂ hC x
        (fun z ↦ killedRootBinomialMoment D L₁ C₁ L₂ C₂ z p)).symm

/-- The full original finite-walk completion input is proved without a moment or Markov input. -/
theorem finite_root_completion_input_internal : FiniteRootCompletionInput := by
  intro D L₁ C₁ L₂ C₂ hL₁ hL₂ _ _ hC hB x
  exact ⟨finite_root_completion_support_internal D L₁ C₁ L₂ C₂ hL₁ hL₂ x,
    fun p ↦ killed_root_binomial_recurrence_internal D L₁ C₁ L₂ C₂ hL₁ hL₂ hC hB x p⟩

end SRWTightness
