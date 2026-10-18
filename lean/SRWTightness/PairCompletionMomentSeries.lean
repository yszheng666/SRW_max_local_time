import SRWTightness.PairCompletionHistory
import SRWTightness.RootMomentPathIntegral
import SRWTightness.CountableRestartMeasurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The future factorial count shifted from a deterministic observed position is measurable. -/
theorem measurable_shifted_root_choose (D L₁ C₁ L₂ C₂ : Finset Site)
    (x : Site) (n p : ℕ) : Measurable (fun ω ↦
      ((wordMarkRootCount L₁ C₁ (killedWordMark D (x + position ω n) (shift n ω)) +
        wordMarkRootCount L₂ C₂ (killedWordMark D (x + position ω n) (shift n ω))).choose p :
          ℝ≥0∞)) := by
  have hξ : Measurable (fun ω ↦ x + position ω n) :=
    (history_measurable_restart_site x n).mono (history.le n) le_rfl
  exact measurable_countable_state_restart _ hξ n _
    (fun z ↦ measurable_killed_root_choose D L₁ C₁ L₂ C₂ z p)

/-- Nonnegative future rewards at completion events integrate to actual restart moments termwise. -/
theorem pair_completion_future_moment_series (D L₁ C₁ L₂ C₂ : Finset Site)
    (x : Site) (p : ℕ) :
    (∫⁻ ω, ∑' n, (pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n).indicator
      (fun υ ↦ ((wordMarkRootCount L₁ C₁
        (killedWordMark D (x + position υ n) (shift n υ)) + wordMarkRootCount L₂ C₂
          (killedWordMark D (x + position υ n) (shift n υ))).choose p : ℝ≥0∞)) ω ∂pathLaw) =
    ∑' n, ∫⁻ ω, killedRootBinomialMoment D L₁ C₁ L₂ C₂ (x + position ω n) p
      ∂pathLaw.restrict (pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n) := by
  have hE (n : ℕ) : MeasurableSet (pairCompletionHistoryEvent D L₁ C₁ L₂ C₂ x n) :=
    (history.le n) _ (measurable_pair_completion_history_event D L₁ C₁ L₂ C₂ x n)
  rw [lintegral_tsum (fun n ↦
    ((measurable_shifted_root_choose D L₁ C₁ L₂ C₂ x n p).indicator (hE n)).aemeasurable)]
  apply tsum_congr
  intro n
  rw [lintegral_indicator (hE n)]
  exact history_restart_root_binomial_moment D L₁ C₁ L₂ C₂ n _
    (measurable_pair_completion_history_event D L₁ C₁ L₂ C₂ x n) _
      (history_measurable_restart_site x n) p

end SRWTightness
