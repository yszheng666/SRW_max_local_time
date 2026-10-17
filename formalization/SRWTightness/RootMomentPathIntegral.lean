import SRWTightness.RootBinomialMoment
import SRWTightness.HistoryRestartIntegral

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The actual killed-walk factorial-moment functional is globally measurable. -/
theorem measurable_killed_root_choose (D L₁ C₁ L₂ C₂ : Finset Site) (x : Site) (p : ℕ) :
    Measurable (fun ω ↦ ((wordMarkRootCount L₁ C₁ (killedWordMark D x ω) +
      wordMarkRootCount L₂ C₂ (killedWordMark D x ω)).choose p : ℝ≥0∞)) :=
  (measurable_of_countable (fun Y : WordMark ↦
    ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y).choose p : ℝ≥0∞))).comp
      (measurable_killedWordMark D x)

/-- The original ordered-word factorial moment is exactly the actual path integral. -/
theorem killed_root_binomial_moment_path_integral (D L₁ C₁ L₂ C₂ : Finset Site)
    (x : Site) (p : ℕ) :
    killedRootBinomialMoment D L₁ C₁ L₂ C₂ x p =
      ∫⁻ ω, ((wordMarkRootCount L₁ C₁ (killedWordMark D x ω) +
        wordMarkRootCount L₂ C₂ (killedWordMark D x ω)).choose p : ℝ≥0∞) ∂pathLaw := by
  unfold killedRootBinomialMoment rootBinomialMoment killedWordMarkLaw
  exact lintegral_map (measurable_of_countable _) (measurable_killedWordMark D x)

/-- On any past event, the future factorial moment is the actual moment at the restart site. -/
theorem history_restart_root_binomial_moment (D L₁ C₁ L₂ C₂ : Finset Site)
    (n : ℕ) (E : Set Sample) (hE : MeasurableSet[history n] E)
    (ξ : Sample → Site) (hξ : Measurable[history n] ξ) (p : ℕ) :
    (∫⁻ ω, ((wordMarkRootCount L₁ C₁ (killedWordMark D (ξ ω) (shift n ω)) +
      wordMarkRootCount L₂ C₂ (killedWordMark D (ξ ω) (shift n ω))).choose p : ℝ≥0∞)
        ∂pathLaw.restrict E) =
      ∫⁻ ω, killedRootBinomialMoment D L₁ C₁ L₂ C₂ (ξ ω) p ∂pathLaw.restrict E := by
  rw [lintegral_history_restart n E hE ξ hξ _
    (fun z ↦ measurable_killed_root_choose D L₁ C₁ L₂ C₂ z p)]
  simp only [← killed_root_binomial_moment_path_integral]

end SRWTightness
