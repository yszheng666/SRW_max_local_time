import SRWTightness.SourcePairObservationIndex
import SRWTightness.SourcePairDeficitDistance
import SRWTightness.SourcePairPrefixAtNode

namespace SRWTightness

/-- The actual late-pair distance range supplies a retained node, its logarithmic deficit, and the prefix barrier. -/
theorem source_late_pair_prefix (t A γ ρ : ℝ) (b : Site)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (hρ : A < ρ) (hcut : ρ ≤ A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio))
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (p : Sample × (ℕ → GaussianCoefficientSpace))
    (hp : p ∈ sourceLocalTimeSuccessEvent t A γ b I z) :
    ∃ i : ℕ, i ≤ I ∧ 4 * ρ ≤ A * diskEnergyGapRatio ^ i ∧
      A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * ρ ∧
      (∀ j : ℕ, j < i → A * diskEnergyGapRatio ^ j < 4 * ρ) ∧
      let v := sourceObservationTime t A I (I - i + 1)
      let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) p.1
      let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - Real.sqrt (2 * (k : ℝ))
      let d := sourceLowerTime (sourceLowerRadius t)
      |(d - v) - Real.log ρ| ≤ sourceEquilibriumTimeError + sourceLowerTimeError +
        Real.log (4 * diskEnergyGapRatio) ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ v →
        sourceBridgedPath t A I (sourceWalkObservation t A b I z k p.1) p.2 s ≤ q) ∧
      sourceBridgedPath t A I (sourceWalkObservation t A b I z k p.1) p.2 v ≤
        q - (d - v) ^ γ := by
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  obtain ⟨i, hi, hlo, hhi, hfirst⟩ := source_pair_observation_index A ρ I (by linarith) hρ hcut
  refine ⟨i, hi, hlo, hhi, hfirst, ?_⟩
  have hd := source_pair_deficit_log_distance b t A ρ hA ht I hI i hi (by linarith) hlo hhi
  have hb := source_success_pair_prefix_at_node t A γ b hA ht hlog I hI z p hp
    (⟨I - i, by omega⟩ : Fin (I + 1))
  exact ⟨hd, hb⟩

end SRWTightness
