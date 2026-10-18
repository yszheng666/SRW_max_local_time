import SRWTightness.SourceSuccessCount
import SRWTightness.SourceCenteredSuccessEvent

open MeasureTheory
namespace SRWTightness

/-- The successful-site count expressed using one common observation level and center events. -/
noncomputable def sourceCenteredSuccessCount (t A γ : ℝ) (I : ℕ)
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace)) : ℝ :=
  ∑ b : sourceCandidateAnnulus (Real.exp t),
    (sourceCenteredSuccessEvent t A γ b I).indicator (fun _ ↦ 1) p

/-- The original dependent-level count equals the common-level count pointwise. -/
theorem source_success_count_eq_centered (t A γ : ℝ) (I₀ : ℕ)
    (I : sourceCandidateAnnulus (Real.exp t) → ℕ)
    (z : ∀ b : sourceCandidateAnnulus (Real.exp t),
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b)))
    (hI₀ : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀)
    (hI : ∀ (b : sourceCandidateAnnulus (Real.exp t)) (i : ℕ),
      A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I b)
    (hz : ∀ b, (z b : Site) = (b : Site)) :
    sourceSuccessCount (Real.exp t) A γ I z = sourceCenteredSuccessCount t A γ I₀ := by
  funext p
  unfold sourceSuccessCount sourceCenteredSuccessCount
  rw [Real.log_exp]
  apply Finset.sum_congr rfl
  intro b hb
  have he := source_centered_success_event_eq t A γ b (I b) (z b) (hz b)
  have hl := source_observation_level_unique t A (I b) I₀ (hI b) hI₀
  rw [← he, hl]

end SRWTightness
