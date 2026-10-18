import SRWTightness.SourceFullPairSum
import SRWTightness.SourceSharedClosePairs
import SRWTightness.SourceCenteredSuccessEvent

open MeasureTheory Filter
namespace SRWTightness

/-- The close-pair sum in the same Cartesian representation as the other distance regimes. -/
noncomputable def sourceCenteredCloseContribution (t A γ : ℝ) (I : ℕ) : ℝ :=
  ∑ p ∈ sourceClosePairs (sourceCandidateAnnulus (Real.exp t)) A, sourceEnlargedLaw.real
    (sourceCenteredSuccessEvent t A γ p.1 I ∩ sourceCenteredSuccessEvent t A γ p.2 I)

/-- The original close-neighbor sum equals the canonical Cartesian close-pair sum. -/
theorem source_close_contribution_eq_centered (t A γ : ℝ) (I₀ : ℕ)
    (I : sourceCandidateAnnulus (Real.exp t) → ℕ)
    (z : ∀ b : sourceCandidateAnnulus (Real.exp t),
      translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b)))
    (hI₀ : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀)
    (hI : ∀ (b : sourceCandidateAnnulus (Real.exp t)) (i : ℕ),
      A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I b)
    (hz : ∀ b, (z b : Site) = (b : Site)) :
    sourceClosePairContribution (Real.exp t) A γ I z =
      sourceCenteredCloseContribution t A γ I₀ := by
  classical
  have he (b : sourceCandidateAnnulus (Real.exp t)) :
      sourceSiteSuccessEvent (Real.log (Real.exp t)) A γ b (I b) (z b) =
        sourceCenteredSuccessEvent t A γ b I₀ := by
    rw [Real.log_exp, ← source_centered_success_event_eq t A γ b (I b) (z b) (hz b),
      source_observation_level_unique t A (I b) I₀ (hI b) hI₀]
  unfold sourceClosePairContribution
  simp_rw [he]
  unfold sourceCenteredCloseContribution sourceClosePairs latticeCloseNeighbors
  simp only [Finset.sum_filter]
  exact source_subtype_pair_sum_product (sourceCandidateAnnulus (Real.exp t))
    (fun p ↦ if Real.sqrt (normSq (p.2 - p.1)) ≤ A then sourceEnlargedLaw.real
      (sourceCenteredSuccessEvent t A γ p.1 I₀ ∩ sourceCenteredSuccessEvent t A γ p.2 I₀) else 0)

/-- The shared one-point bound controls canonical close pairs at every valid common level. -/
theorem source_centered_close_pairs_bounded (J A γ : ℝ) (hγ : 0 ≤ γ)
    (hOne : SourceOnePointEstimate J A γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in atTop, ∀ I₀ : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀) →
      sourceCenteredCloseContribution t A γ I₀ ≤ K := by
  obtain ⟨K, hA, hK, hb⟩ := source_close_pairs_bounded_shared J A γ hγ hOne
  refine ⟨K, hK, ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually hb] with t ht
  intro I₀ hI₀
  obtain ⟨I, z, hz, hI, hp⟩ := ht
  have hI' : ∀ (b : sourceCandidateAnnulus (Real.exp t)) (i : ℕ),
      A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I b := by
    simpa only [Real.log_exp] using hI
  rw [source_close_contribution_eq_centered t A γ I₀ I z hI₀ hI' hz] at hp
  exact hp

end SRWTightness
