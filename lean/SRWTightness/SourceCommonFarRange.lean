import SRWTightness.SourceCommonFarGeneration
import SRWTightness.SourceRootGWHorizon

open Filter
namespace SRWTightness

/-- Equation (9.15): far pairs have a valid common generation strictly below the source horizon. -/
theorem source_common_far_range :
    ∃ C : ℝ, ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (I j : ℕ) (b w : Site), 0 < A → b ≠ w →
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) < Real.sqrt (normSq (w - b)) →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      (j : ℝ) ≤ (sourceCoarseGeneration t : ℝ) + 1 + 6 * Real.log t +
          Real.log (8 * diskEnergyGapRatio ^ 2) - (sourceCommonPairGap t : ℝ) ∧
      (sourceCoarseGeneration t : ℝ) + 1 + 6 * Real.log t +
          Real.log (8 * diskEnergyGapRatio ^ 2) - (sourceCommonPairGap t : ℝ) ≤
        (sourceCoarseGeneration t : ℝ) - 4 * Real.log t + C ∧
      (sourceCoarseGeneration t : ℝ) - 4 * Real.log t + C < (sourceCoarseGeneration t : ℝ) ∧
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
  let C := Real.log (8 * diskEnergyGapRatio ^ 2)
  have hC : 0 < C := by
    apply Real.log_pos
    nlinarith [diskEnergyGapRatio_gt_four]
  refine ⟨C, ?_⟩
  filter_upwards [source_root_gw_horizon_large, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (C + 1))] with t hn ht hl
  intro A I j b w hA hbw hI hsep hi
  obtain ⟨hρ, houter⟩ := source_common_distance_range t b w j hbw hi
  have hj := source_common_far_generation t A _ I j (by linarith) hA (by linarith)
    hI hsep hi
  have hℓ : 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by omega
  have hdepth : (sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) =
      (sourceCoarseGeneration t : ℝ) + 1 := by
    have hh := hn.2
    rw [Nat.cast_sub hℓ, Nat.cast_one] at hh
    linarith
  rw [hdepth] at hj
  have hgap := (sourceCommonPairGap_bounds t ht).1
  have hmid : (sourceCoarseGeneration t : ℝ) + 1 + 6 * Real.log t + C -
      (sourceCommonPairGap t : ℝ) ≤ (sourceCoarseGeneration t : ℝ) - 4 * Real.log t + C := by
    linarith
  have hlast : (sourceCoarseGeneration t : ℝ) - 4 * Real.log t + C <
      (sourceCoarseGeneration t : ℝ) := by linarith
  refine ⟨hj, hmid, hlast, ?_⟩
  have hh : (j : ℝ) + 1 ≤ (sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) := by
    change (j : ℝ) ≤ (sourceCoarseGeneration t : ℝ) + 1 + 6 * Real.log t + C -
      (sourceCommonPairGap t : ℝ) at hj
    linarith
  exact_mod_cast hh

end SRWTightness
