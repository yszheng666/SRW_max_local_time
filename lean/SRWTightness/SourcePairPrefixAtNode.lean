import SRWTightness.SourcePairPrefix
import SRWTightness.SourceTerminalCutoffRange

namespace SRWTightness

/-- Every retained source observation time satisfies the late-pair prefix restrictions. -/
theorem source_success_pair_prefix_at_node (t A γ : ℝ) (b : Site)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (p : Sample × (ℕ → GaussianCoefficientSpace))
    (hp : p ∈ sourceLocalTimeSuccessEvent t A γ b I z) (i : Fin (I + 1)) :
    let v := sourceObservationTime t A I (i.val + 1)
    let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) p.1
    let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - Real.sqrt (2 * (k : ℝ))
    let d := sourceLowerTime (sourceLowerRadius t)
    (∀ s : ℝ, 0 ≤ s → s ≤ v →
      sourceBridgedPath t A I (sourceWalkObservation t A b I z k p.1) p.2 s ≤ q) ∧
    sourceBridgedPath t A I (sourceWalkObservation t A b I z k p.1) p.2 v ≤
      q - (d - v) ^ γ := by
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hs : ∀ j < I + 1, sourceObservationTime t A I j <
      sourceObservationTime t A I (j + 1) := fun j hj ↦ by linarith [hg j (by omega)]
  have hlo := timeGridTime_mono (sourceObservationTime t A I) (I + 1) hs
    (show 0 ≤ i.val + 1 by omega) (show i.val + 1 ≤ I + 1 by omega)
  have hup := timeGridTime_mono (sourceObservationTime t A I) (I + 1) hs
    (show i.val + 1 ≤ I + 1 by omega) le_rfl
  rw [sourceObservationTime_zero] at hlo
  have hc := (source_terminal_cutoff_range b t A hA ht I hI).1
  have hd : sourceObservationTime t A I (I + 1) ≤
      sourceLowerTime (sourceLowerRadius t) := by
    have hh := (abs_le.mp hc).1
    linarith
  exact source_success_pair_prefix t A γ b I z p hp _ hlo hup (hup.trans hd)

end SRWTightness
