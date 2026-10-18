import SRWTightness.SourceUpperBlockCapacity
import SRWTightness.FiniteRecordReferenceMeasure
import SRWTightness.ReferenceMarkGWTree

open Filter MeasureTheory

namespace SRWTightness

/-- Reference occupation marks for the actual upper block in the source terminal killing disk. -/
noncomputable def sourceUpperBlockMarkLaw (t : ℝ) (b : Site) :
    Measure (Mark (sourceUpperBlock t b)) :=
  referenceMarkLaw
    (translateFinset b (diskFinset (Real.exp 1 * sourceUpperRadius t + sourceUpperBuffer t)))
    (sourceUpperBlock t b) (sourceUpperIntensity t)

/-- Upper reference trees are normalized and have the standard geometric population law. -/
theorem source_upper_block_reference_measure :
    ∀ᶠ t : ℝ in atTop, ∀ b : Site, MarkedGWTreeInput (Mark (sourceUpperBlock t b)) →
      ∀ n : ℕ, ∀ [MeasurableSpace (FiniteExcursionRecord (Mark (sourceUpperBlock t b)) n)]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark (sourceUpperBlock t b)) n)],
      IsProbabilityMeasure (finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b) n) ∧
      ∀ s : Set GeometricGWRecord,
        finiteRecordReferenceMeasure (sourceUpperBlockMarkLaw t b) n
          {r | finiteRecordPopulationList n r ∈ s} = geometricGWRecordLaw 1 n s := by
  filter_upwards [source_upper_block_capacity_half,
    source_upper_record_scale_conditions 0 0 0 (by norm_num)] with t hcap hs
  intro b hmarked n inst₁ inst₂
  have hh := source_reference_marked_gw_law b (sourceUpperRadius t) (sourceUpperBuffer t)
    (sourceUpperBlock t b) hmarked (Real.exp_pos _) (by linarith [hs.1])
    (by linarith [hs.1, hs.2.1]) (hcap b) n
  constructor
  · constructor
    rw [finiteRecordReferenceMeasure_apply]
    exact hh.1
  · intro s
    rw [finiteRecordReferenceMeasure_apply]
    exact hh.2 s

end SRWTightness
