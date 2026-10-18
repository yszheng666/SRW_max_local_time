import SRWTightness.FiniteSuccessIntegrable
import SRWTightness.SourceCenteredSuccessCount
import SRWTightness.SourcePairCenterChoice

open MeasureTheory Filter
namespace SRWTightness

/-- The canonical successful-site count is nonnegative on every path and auxiliary sample. -/
theorem source_centered_success_count_nonneg (t A γ : ℝ) (I : ℕ)
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace)) :
    0 ≤ sourceCenteredSuccessCount t A γ I p := by
  apply Finset.sum_nonneg
  intro b hb
  exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) p

/-- The actual canonical count and its square are integrable at every valid common cutoff. -/
theorem source_canonical_count_integrable :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ), 1 ≤ A → 0 ≤ γ → ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      Integrable (sourceCenteredSuccessCount t A γ I) sourceEnlargedLaw ∧
      Integrable (fun p ↦ sourceCenteredSuccessCount t A γ I p ^ 2) sourceEnlargedLaw := by
  filter_upwards [source_local_time_success_nullMeasurable] with t ht
  intro A γ hA hγ I hI
  obtain ⟨z, hz⟩ := source_pair_center_choice A I (by linarith)
  have hpos : 1 ≤ A * diskEnergyGapRatio ^ I := by
    have hp : 1 ≤ diskEnergyGapRatio ^ I :=
      one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
    nlinarith
  have hnull (b : sourceCandidateAnnulus (Real.exp t)) :
      NullMeasurableSet (sourceCenteredSuccessEvent t A γ b I) sourceEnlargedLaw := by
    rw [source_centered_success_event_eq t A γ b I (z b) (hz b)]
    apply source_site_success_nullMeasurable
    have hb := (mem_sourceCandidateAnnulus _ (Real.exp_pos _) b).mp b.property
    exact ht A γ b I (z b) hγ hpos ((hI I).mpr le_rfl) hb.1 hb.2
  exact ⟨finite_success_integrable sourceEnlargedLaw Finset.univ
      (fun b : sourceCandidateAnnulus (Real.exp t) ↦ sourceCenteredSuccessEvent t A γ b I)
      (fun b _ ↦ hnull b),
    finite_success_square_integrable sourceEnlargedLaw Finset.univ
      (fun b : sourceCandidateAnnulus (Real.exp t) ↦ sourceCenteredSuccessEvent t A γ b I)
      (fun b _ ↦ hnull b)⟩

end SRWTightness
