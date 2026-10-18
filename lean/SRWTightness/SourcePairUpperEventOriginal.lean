import SRWTightness.SourcePairUpperEvent
import SRWTightness.SourcePairReferenceCoordinates

open MeasureTheory Filter

namespace SRWTightness

/-- The complete retained event is exactly the high-site event with the original continuous prefix. -/
theorem sourcePairUpperEvent_original_ae_iff (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (At q f : ℝ) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ,
      ∀ (x : PairObservationIndex (I - i + 1) → ℝ) (y : Fin ((I + 1) + 1) → ℝ),
      (∀ j, x (.inl j) = y (sourcePairAverageIndex I i j)) →
      ((x, ω) ∈ sourcePairUpperEvent t A I i At q f ↔
        At ≤ x (.inr false) ∧ At ≤ x (.inr true) ∧
        sourceBridgedPath t A I y ω (sourceObservationTime t A I (I - i + 1)) ≤ q - f ∧
        ∀ v : ℝ, 0 ≤ v → v ≤ sourceObservationTime t A I (I - i + 1) →
          sourceBridgedPath t A I y ω v ≤ q) := by
  filter_upwards [sourcePairUpperEvent_ae_iff t A I i At q f] with ω hω
  intro x y hxy
  rw [hω x]
  have hn : sourceBridgedPath t A I y ω (sourceObservationTime t A I (I - i + 1)) =
      x (.inl (Fin.last (I - i))) - 2 * sourceObservationTime t A I (I - i + 1) := by
    rw [hxy (Fin.last (I - i))]
    simpa only [sourcePairAverageIndex, Fin.val_last, Fin.castSucc, Fin.castAdd, Fin.castLE]
      using sourceBridgedPath_node t A hA ht I hI y ω ⟨I - i, by omega⟩
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr
  · rw [hn]
    constructor <;> intro h <;> linarith
  · constructor
    · intro hp v hv hvtop
      have he := pairObservationExtension_prefix t A I i hA ht hI x y hxy ω v hvtop
      simpa only [he] using hp v hv hvtop
    · intro hp v hv hvtop
      rw [pairObservationExtension_prefix t A I i hA ht hI x y hxy ω v hvtop]
      exact hp v hv hvtop

/-- For actual marks the retained event has the original two site variables and full average path. -/
theorem sourcePairUpperEvent_reference_ae_iff (b : Site) (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (D M : Finset Site) (z y : M) (k : ℕ) (α g u At q f : ℝ) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ, ∀ Y : MarkSamples M k,
      let x := fun j ↦ normalizedWeightedSum M k α g u
        (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j) Y
      let full := fun j : Fin ((I + 1) + 1) ↦
        normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
          z k α g u (diskObservationIndex (I + 1) j) Y
      (x, ω) ∈ sourcePairUpperEvent t A I i At q f ↔
        At ≤ normalizedMarkSum M k α g u z Y ∧ At ≤ normalizedMarkSum M k α g u y Y ∧
        sourceBridgedPath t A I full ω (sourceObservationTime t A I (I - i + 1)) ≤ q - f ∧
        ∀ v : ℝ, 0 ≤ v → v ≤ sourceObservationTime t A I (I - i + 1) →
          sourceBridgedPath t A I full ω v ≤ q := by
  filter_upwards [sourcePairUpperEvent_original_ae_iff t A I i hA ht hI At q f] with ω hω
  intro Y
  dsimp only
  have hh := hω
    (fun j ↦ normalizedWeightedSum M k α g u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j) Y)
    (fun j ↦ normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
      z k α g u (diskObservationIndex (I + 1) j) Y)
    (source_pair_reference_coordinates b A I i D M z y k α g u Y)
  simpa only [pairObservationWeight, normalizedWeightedSum_observationWeight,
    normalizedObservation] using hh

end SRWTightness
