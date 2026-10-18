import SRWTightness.ExternalMarkedGWJoint
import SRWTightness.SourceCommonPairObservationUniform
import SRWTightness.SourceCommonPairRadiusLower
import SRWTightness.SourceTerminalCapacityHalf
import SRWTightness.SourceScaleThreshold

open MeasureTheory Filter
open scoped ENNReal
namespace SRWTightness

/-- The common source law satisfies the joint population and independent terminal-mark interface. -/
theorem source_common_reference_joint :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ [MeasurableSpace (List (Mark (sourceCommonPairObservation b w)))]
        [MeasurableSingletonClass (List (Mark (sourceCommonPairObservation b w)))],
      MarkedGWJointInput (Mark (sourceCommonPairObservation b w)) →
      ∀ (s : Set GeometricGWRecord)
        (E : GeometricGWRecord → Set (List (Mark (sourceCommonPairObservation b w)))),
      let μ := referenceMarkLaw (sourceCommonPairDomain t b j)
        (sourceCommonPairObservation b w) (sourceCommonPairIntensity t j)
      finiteRecordReferenceMass μ j {r | finiteRecordPopulationList j r ∈ s ∧
        finiteRecordLeaves j r ∈ E (finiteRecordPopulationList j r)} =
        ∫⁻ g in s, independentForestLaw μ (geometricGWPopulation g j) (E g)
          ∂geometricGWRecordLaw 1 j := by
  filter_upwards [source_common_pair_observation_uniform,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t ht hs
  intro b w j hbw hi hd inst₁ inst₂ hinput s E
  dsimp only
  have hg := ht b w j hbw hi
  have hm : 70 ≤ sourceCommonPairInnerRadius t j :=
    ((sourceScaleThreshold_conditions t 4 (by norm_num) hs).2.2.1).trans
      (sourceCommonPairInnerRadius_ge_lower t j hd)
  have hα := (sourceCommonPairIntensity_bounds t j hm).1.le
  have hc := source_terminal_capacity_half b (sourceCommonPairInnerRadius t j) 14
    (2 * Real.sqrt (normSq (w - b))) (sourceCommonPairObservation b w)
    hg.1 hg.2.1 (by norm_num) (by linarith) (Finset.Subset.refl _) hg.2.2
  have hcap : sourceCommonPairIntensity t j *
      capacity (sourceCommonPairDomain t b j) (sourceCommonPairObservation b w) ≤ 1 := by
    rw [sourceCommonPairDomain_eq]
    exact hc.trans (by norm_num)
  exact hinput _ (referenceMarkLaw_isProbabilityMeasure _ _ _ hα hcap) j s E

end SRWTightness
