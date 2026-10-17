import SRWTightness.SourceCommonFarGeneration
import SRWTightness.SourceRootGWHorizon
import SRWTightness.SourceSignedDistanceIndex

open Filter
namespace SRWTightness

/-- Equation (9.15) for the signed manuscript index, including negative common levels. -/
theorem source_signed_common_range :
    ∃ C : ℝ, ∀ᶠ t : ℝ in atTop, ∀ (A ρ : ℝ) (I : ℕ), 0 < A → 0 < ρ →
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) < ρ →
      (sourceSignedDistanceIndex t ρ : ℝ) - (sourceCommonPairGap t : ℝ) ≤
        (sourceCoarseGeneration t : ℝ) + 1 + 6 * Real.log t +
          Real.log (8 * diskEnergyGapRatio ^ 2) - (sourceCommonPairGap t : ℝ) ∧
      (sourceCoarseGeneration t : ℝ) + 1 + 6 * Real.log t +
          Real.log (8 * diskEnergyGapRatio ^ 2) - (sourceCommonPairGap t : ℝ) ≤
        (sourceCoarseGeneration t : ℝ) - 4 * Real.log t + C ∧
      (sourceCoarseGeneration t : ℝ) - 4 * Real.log t + C < (sourceCoarseGeneration t : ℝ) := by
  let C := Real.log (8 * diskEnergyGapRatio ^ 2)
  have hC : 0 < C := by apply Real.log_pos; nlinarith [diskEnergyGapRatio_gt_four]
  refine ⟨C, ?_⟩
  filter_upwards [source_root_gw_horizon_large, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (C + 1))] with t hn ht hl
  intro A ρ I hA hρ hI hsep
  have hu := source_far_distance_index t A ρ I ht hA hρ hI hsep
  have hℓ : 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by omega
  have hdepth : (sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) =
      (sourceCoarseGeneration t : ℝ) + 1 := by
    have hh := hn.2
    rw [Nat.cast_sub hℓ, Nat.cast_one] at hh
    linarith
  rw [hdepth] at hu
  have hsigned : (sourceSignedDistanceIndex t ρ : ℝ) ≤
      (sourceCommonPairDistanceIndex t ρ : ℝ) := by
    exact_mod_cast source_signed_distance_le_natural t ρ
  have hgap := (sourceCommonPairGap_bounds t ht).1
  refine ⟨by linarith, ?_, ?_⟩
  · dsimp [C]
    linarith
  · linarith

end SRWTightness
