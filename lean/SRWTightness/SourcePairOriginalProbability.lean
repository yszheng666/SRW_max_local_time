import SRWTightness.SourcePairUpperEventOriginal
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory Filter

namespace SRWTightness

/-- The two original marked site variables and the full continuous average prefix. -/
def sourcePairOriginalEvent (b : Site) (t A : ℝ) (I i : ℕ)
    (D M : Finset Site) (z y : M) (k : ℕ) (α g u At q f : ℝ) :
    Set (MarkSamples M k × (ℕ → GaussianCoefficientSpace)) :=
  {p | let full := fun j : Fin ((I + 1) + 1) ↦
      normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
        z k α g u (diskObservationIndex (I + 1) j) p.1
    At ≤ normalizedMarkSum M k α g u z p.1 ∧
    At ≤ normalizedMarkSum M k α g u y p.1 ∧
    sourceBridgedPath t A I full p.2 (sourceObservationTime t A I (I - i + 1)) ≤ q - f ∧
    ∀ v : ℝ, 0 ≤ v → v ≤ sourceObservationTime t A I (I - i + 1) →
      sourceBridgedPath t A I full p.2 v ≤ q}

/-- Passing to retained coordinates preserves the probability of the original prefix event. -/
theorem source_pair_original_probability (b : Site) (t A : ℝ) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (D M : Finset Site) (z y : M) (k : ℕ) (α g u At q f : ℝ)
    (μ : Measure (MarkSamples M k)) [SFinite μ] :
    let F := fun Y j ↦ normalizedWeightedSum M k α g u
      (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j) Y
    (μ.prod (independentBridgeLaw ℕ)).real
      (sourcePairOriginalEvent b t A I i D M z y k α g u At q f) =
    ((μ.map F).prod (independentBridgeLaw ℕ)).real (sourcePairUpperEvent t A I i At q f) := by
  dsimp only
  let F := fun Y j ↦ normalizedWeightedSum M k α g u
    (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j) Y
  have hF : Measurable F := by
    dsimp [F]
    unfold normalizedWeightedSum normalizedMarkSum
    fun_prop
  have hm := Measure.map_prod_map μ (independentBridgeLaw ℕ) hF measurable_id
  rw [Measure.map_id] at hm
  rw [hm, map_measureReal_apply (hF.prodMap measurable_id)
    (sourcePairUpperEvent_measurable t A I i At q f)]
  have hh := (Measure.quasiMeasurePreserving_snd
    (μ := μ) (ν := independentBridgeLaw ℕ)).ae
    (sourcePairUpperEvent_reference_ae_iff b t A I i hA ht hI D M z y k α g u At q f)
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hh] with p hp
  exact propext (hp p.1).symm

end SRWTightness
