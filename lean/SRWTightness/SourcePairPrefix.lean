import SRWTightness.SourceWalkSuccessEvent

namespace SRWTightness

/-- The continuous success barrier supplies the flat prefix and endpoint deficit used for late pairs. -/
theorem source_success_pair_prefix (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (p : Sample × (ℕ → GaussianCoefficientSpace))
    (hp : p ∈ sourceLocalTimeSuccessEvent t A γ b I z)
    (v : ℝ) (hv : 0 ≤ v) (hvtop : v ≤ sourceObservationTime t A I (I + 1))
    (hvd : v ≤ sourceLowerTime (sourceLowerRadius t)) :
    let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) p.1
    let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - Real.sqrt (2 * (k : ℝ))
    let d := sourceLowerTime (sourceLowerRadius t)
    (∀ s : ℝ, 0 ≤ s → s ≤ v →
      sourceBridgedPath t A I (sourceWalkObservation t A b I z k p.1) p.2 s ≤ q) ∧
    sourceBridgedPath t A I (sourceWalkObservation t A b I z k p.1) p.2 v ≤
      q - (d - v) ^ γ := by
  dsimp only
  have hterminal := hp.2.2.2
  have hpath := hterminal.2.2.2.2
  constructor
  · intro s hs hsv
    have hb := hpath s hs (hsv.trans hvtop)
    have hr : 0 ≤ (sourceLowerTime (sourceLowerRadius t) - s) ^ γ :=
      Real.rpow_nonneg (sub_nonneg.mpr (hsv.trans hvd)) _
    linarith
  · exact hpath v hv hvtop

end SRWTightness
