import SRWTightness.SourceCenteredPairContribution
import SRWTightness.SourcePairCenterChoice

open MeasureTheory Filter
namespace SRWTightness

/-- The canonical successful-site count has the full canonical pair sum as its second moment
at every valid common level; dependent sitewise choices have been eliminated. -/
theorem source_canonical_second_moment :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ), 1 ≤ A → 0 ≤ γ → ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      (∫ p, sourceCenteredSuccessCount t A γ I p ^ 2 ∂sourceEnlargedLaw) =
        sourceCenteredPairContribution t A γ I := by
  filter_upwards [source_centered_success_second_moment] with t ht
  intro A γ hA hγ I hI
  obtain ⟨z, hz⟩ := source_pair_center_choice A I (by linarith)
  have hpos : 1 ≤ A * diskEnergyGapRatio ^ I := by
    have hp : 1 ≤ diskEnergyGapRatio ^ I :=
      one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
    nlinarith
  exact ht A γ hγ I (fun _ ↦ I) (fun b ↦ z b) hI (fun _ ↦ hI)
    (fun b ↦ hz b) (fun _ ↦ hpos)

end SRWTightness
