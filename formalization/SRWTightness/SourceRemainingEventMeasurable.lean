import SRWTightness.SourceRemainingEvents
import SRWTightness.SourceReferenceMixtureSuccess

open MeasureTheory
namespace SRWTightness

/-- The two-site tagged remaining event is measurable, including both terminal bridge conditions. -/
theorem sourceTaggedRemainingEvent_measurable (t A γ : ℝ) (b w : Site) (I₀ I₁ ν : ℕ)
    (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
    (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))
    [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
    [MeasurableSingletonClass (List (Mark
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
    [MeasurableSpace (List (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
    [MeasurableSingletonClass (List (Mark
      (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
    [MeasurableSpace (SourceFineRecord t
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
    [MeasurableSingletonClass (SourceFineRecord t
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
    [MeasurableSpace (SourceFineRecord t
      (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
    [MeasurableSingletonClass (SourceFineRecord t
      (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
    [MeasurableSpace (List (SourceFineRecord t
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
    [MeasurableSingletonClass (List (SourceFineRecord t
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
    [MeasurableSpace (List (SourceFineRecord t
      (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
    [MeasurableSingletonClass (List (SourceFineRecord t
      (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
    (h : ExteriorPathRecord) (k l : ℕ) :
    MeasurableSet (sourceTaggedRemainingEvent t A γ b w I₀ I₁ ν z₀ z₁ h k l) := by
  letI := finiteExcursionRecord_countable
    (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))))
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
  letI := finiteExcursionRecord_countable
    (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))))
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
  apply MeasurableSet.inter
  · apply (sourceContinuationForestEvent_measurable t A γ b I₀ z₀ ν _ k).preimage
    exact ((measurable_of_countable (fun r ↦ (orderedTaggedForests r).1)).comp
      measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  · apply (sourceContinuationForestEvent_measurable t A γ w I₁ z₁ ν _ l).preimage
    exact ((measurable_of_countable (fun r ↦ (orderedTaggedForests r).2)).comp
      measurable_fst).prodMk (measurable_snd.comp measurable_snd)

end SRWTightness
