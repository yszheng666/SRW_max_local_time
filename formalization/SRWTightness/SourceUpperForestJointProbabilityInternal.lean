import SRWTightness.SourceUpperForestJointProbability
import SRWTightness.MarkedGWInputsInternal

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Reference forest success equals the GW-band integral of terminal mark success probabilities. -/
theorem source_upper_forest_joint_probability_internal :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
        [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
        (sourceUpperBlockForestDepth t b))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b)))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
          (sourceUpperBlockForestDepth t b)))],
      ∀ s : ℝ, ∀ J : ℕ,
      independentForestLaw
        (finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b)
          (sourceUpperBlockForestDepth t b)) J (sourceUpperForestSuccess t s b) =
        ∫⁻ g in sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b),
          independentForestLaw (sourceUpperBlockMarkLaw t b)
            (geometricGWPopulation g (sourceUpperBlockForestDepth t b))
            (sourceUpperMarkListHighEvent t s b)
          ∂geometricGWRecordLaw J (sourceUpperBlockForestDepth t b) := by
  filter_upwards [source_upper_block_mark_probability, source_upper_branching_depth_bounds]
    with t hp hd
  intro b hb inst₁ inst₂ inst₃ inst₄ inst₅ inst₆ s J
  have hinput : MarkedGWForestJointInput (Mark (sourceUpperBlock t b)) :=
    marked_gw_forest_joint_input_internal
  letI := hp b
  have he : sourceUpperForestSuccess t s b =
      {rs | forestPopulationList (sourceUpperBlockForestDepth t b) rs ∈
          sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b) ∧
        rs.flatMap (finiteRecordLeaves (sourceUpperBlockForestDepth t b)) ∈
          sourceUpperMarkListHighEvent t s b} := by
    ext rs
    exact source_upper_forest_success_iff_joint t s b (hd b hb).1.le rs
  rw [he]
  exact hinput.forest (sourceUpperBlockMarkLaw t b) inferInstance
    (sourceUpperBlockForestDepth t b) J _ (fun _ ↦ sourceUpperMarkListHighEvent t s b)

end SRWTightness
