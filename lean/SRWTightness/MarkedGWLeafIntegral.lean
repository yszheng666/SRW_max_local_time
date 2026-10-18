import SRWTightness.ExternalMarkedGWJoint
import SRWTightness.FiniteRecordReferenceMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The joint marking law disintegrates every nonnegative leaf weight over the GW population. -/
theorem markedGWJoint_leaf_lintegral {M : Type*} [Countable M] [MeasurableSpace M]
    [MeasurableSingletonClass M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (hinput : MarkedGWJointInput M)
    (μ : Measure M) (hμ : IsProbabilityMeasure μ) (n : ℕ)
    [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)]
    (s : Set GeometricGWRecord) (f : List M → ℝ≥0∞) :
    (∫⁻ r in {r | finiteRecordPopulationList n r ∈ s},
      f (finiteRecordLeaves n r) ∂finiteRecordReferenceMeasure μ n) =
        ∫⁻ g in s, ∫⁻ rs, f rs ∂independentForestLaw μ (geometricGWPopulation g n)
          ∂geometricGWRecordLaw 1 n := by
  letI := finiteExcursionRecord_countable M n
  let κ := fun g : GeometricGWRecord ↦ independentForestLaw μ (geometricGWPopulation g n)
  have hκ : Measurable κ := measurable_of_countable _
  have hl : Measurable (finiteRecordLeaves (M := M) n) := measurable_of_countable _
  have hf : Measurable f := measurable_of_countable _
  have he : ((finiteRecordReferenceMeasure μ n).restrict
      {r | finiteRecordPopulationList n r ∈ s}).map (finiteRecordLeaves n) =
        ((geometricGWRecordLaw 1 n).restrict s).bind κ := by
    ext E hE
    rw [Measure.map_apply hl hE, Measure.restrict_apply (hl hE),
      finiteRecordReferenceMeasure_apply, Measure.bind_apply hE hκ.aemeasurable]
    have hh := hinput μ hμ n s (fun _ ↦ E)
    convert hh using 1
    congr 1
    ext r
    exact and_comm
  rw [← lintegral_map hf hl, he, Measure.lintegral_bind hκ.aemeasurable hf.aemeasurable]

end SRWTightness
