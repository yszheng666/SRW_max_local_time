import SRWTightness.SourceCenteredSuccessCount
import SRWTightness.SourceSuccessSecondMoment

open MeasureTheory Filter
namespace SRWTightness

/-- The full ordered-pair contribution written with canonical center events. -/
noncomputable def sourceCenteredPairContribution (t A γ : ℝ) (I : ℕ) : ℝ :=
  ∑ b : sourceCandidateAnnulus (Real.exp t), ∑ w : sourceCandidateAnnulus (Real.exp t),
    sourceEnlargedLaw.real
      (sourceCenteredSuccessEvent t A γ b I ∩ sourceCenteredSuccessEvent t A γ w I)

/-- Transport of the original ordered-pair sum to any valid common observation level. -/
theorem source_pair_contribution_eq_centered (t A γ : ℝ) (I₀ : ℕ)
    (I : sourceCandidateAnnulus (Real.exp t) → ℕ)
    (z : ∀ b : sourceCandidateAnnulus (Real.exp t),
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b)))
    (hI₀ : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀)
    (hI : ∀ (b : sourceCandidateAnnulus (Real.exp t)) (i : ℕ),
      A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I b)
    (hz : ∀ b, (z b : Site) = (b : Site)) :
    sourcePairContribution (Real.exp t) A γ I z = sourceCenteredPairContribution t A γ I₀ := by
  unfold sourcePairContribution sourceCenteredPairContribution
  rw [Real.log_exp]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro w hw
  rw [← source_centered_success_event_eq t A γ b (I b) (z b) (hz b),
    ← source_centered_success_event_eq t A γ w (I w) (z w) (hz w),
    source_observation_level_unique t A (I b) I₀ (hI b) hI₀,
    source_observation_level_unique t A (I w) I₀ (hI w) hI₀]

/-- The actual source second moment has the common-level pair-sum representation. -/
theorem source_centered_success_second_moment :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ), 0 ≤ γ → ∀ (I₀ : ℕ)
      (I : sourceCandidateAnnulus (Real.exp t) → ℕ)
      (z : ∀ b : sourceCandidateAnnulus (Real.exp t),
        translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b))),
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀) →
      (∀ (b : sourceCandidateAnnulus (Real.exp t)) (i : ℕ),
        A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I b) →
      (∀ b, (z b : Site) = (b : Site)) →
      (∀ b, 1 ≤ A * diskEnergyGapRatio ^ I b) →
      (∫ p, sourceCenteredSuccessCount t A γ I₀ p ^ 2 ∂sourceEnlargedLaw) =
        sourceCenteredPairContribution t A γ I₀ := by
  filter_upwards [Real.tendsto_exp_atTop.eventually source_success_second_moment] with t ht
  intro A γ hγ I₀ I z hI₀ hI hz hpos
  have hcut : ∀ b, 1 ≤ A * diskEnergyGapRatio ^ I b ∧
      A * diskEnergyGapRatio ^ I b ≤ sourceLowerRadius (Real.log (Real.exp t)) /
        (Real.log (Real.exp t)) ^ 6 := by
    intro b
    simpa only [Real.log_exp] using And.intro (hpos b) ((hI b (I b)).mpr le_rfl)
  have hh := ht A γ hγ I z hcut
  rw [source_success_count_eq_centered t A γ I₀ I z hI₀ hI hz,
    source_pair_contribution_eq_centered t A γ I₀ I z hI₀ hI hz] at hh
  exact hh

end SRWTightness
