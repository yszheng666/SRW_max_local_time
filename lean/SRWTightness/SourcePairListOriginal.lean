import SRWTightness.SourcePairListEvent

open MeasureTheory

namespace SRWTightness

/-- One full-measure bridge set identifies the original pair event for every population and leaf list. -/
theorem source_pair_list_original_ae (t A : ℝ) (b : Site) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (f : ℝ) :
    ∀ᵐ β ∂independentBridgeLaw ℕ, ∀ (k : ℕ)
      (rs : List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))),
      let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let u := Real.sqrt (2 * (k : ℝ))
      let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
      (rs, β) ∈ sourcePairListEvent t A b I i z y k f ↔
        (terminalListSamples 0 k rs, β) ∈ sourcePairOriginalEvent b t A I i D M z y k α
          (2 / Real.pi) u (sourceTerminalThreshold t u) q f := by
  have hk (k : ℕ) := sourcePairUpperEvent_reference_ae_iff b t A I i hA ht hI
    (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
    (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) z y k
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi)
    (Real.sqrt (2 * (k : ℝ))) (sourceTerminalThreshold t (Real.sqrt (2 * (k : ℝ))))
    (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - Real.sqrt (2 * (k : ℝ))) f
  filter_upwards [ae_all_iff.mpr hk] with β hβ
  intro k rs
  exact hβ k (terminalListSamples 0 k rs)

end SRWTightness
