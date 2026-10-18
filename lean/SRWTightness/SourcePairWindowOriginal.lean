import SRWTightness.SourcePairWindowEvent

open MeasureTheory Filter

namespace SRWTightness

/-- The retained-vector event tests the original full observation path, not an artificial extension. -/
theorem sourcePairWindowEvent_original_ae_iff (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (At q f : ℝ) (n m l : ℕ) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ,
      ∀ (x : PairObservationIndex (I - i + 1) → ℝ) (y : Fin ((I + 1) + 1) → ℝ),
      (∀ j, x (.inl j) = y (sourcePairAverageIndex I i j)) →
      ((x, ω) ∈ sourcePairWindowEvent t A I i At q f n m l ↔
        x ∈ pairWindow (Fin.last (I - i)) At
          (2 * sourceObservationTime t A I (I - i + 1) + q - f) n m l ∧
        ∀ v : ℝ, 0 ≤ v → v ≤ sourceObservationTime t A I (I - i + 1) →
          sourceBridgedPath t A I y ω v ≤ q) := by
  filter_upwards [sourcePairWindowEvent_ae_iff t A I i At q f n m l] with ω hω
  intro x y hxy
  rw [hω x]
  apply and_congr_right
  intro _
  constructor
  · intro hp v hv hvtop
    have he := pairObservationExtension_prefix t A I i hA ht hI x y hxy ω v hvtop
    simpa only [he] using hp v hv hvtop
  · intro hp v hv hvtop
    rw [pairObservationExtension_prefix t A I i hA ht hI x y hxy ω v hvtop]
    exact hp v hv hvtop

end SRWTightness
