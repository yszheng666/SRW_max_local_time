import SRWTightness.ExternalMarkedGWTree
import SRWTightness.ActualRecordLeaves
import SRWTightness.IndependentForestLaw

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Standard independent terminal marking extension of the finite GW branching product law. -/
def MarkedGWJointInput (M : Type*) [MeasurableSpace M] [MeasurableSingletonClass M]
    [Countable M] [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)] : Prop :=
  ∀ μ : Measure M, IsProbabilityMeasure μ → ∀ (n : ℕ)
    (s : Set GeometricGWRecord) (E : GeometricGWRecord → Set (List M)),
    finiteRecordReferenceMass μ n {r | finiteRecordPopulationList n r ∈ s ∧
      finiteRecordLeaves n r ∈ E (finiteRecordPopulationList n r)} =
        ∫⁻ g in s, independentForestLaw μ (geometricGWPopulation g n) (E g)
          ∂geometricGWRecordLaw 1 n

/-- The joint input implies the old population input; applications need not assume both. -/
theorem markedGWJoint_population {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (hinput : MarkedGWJointInput M) :
    MarkedGWTreeInput M := by
  intro μ hμ n s
  letI := hμ
  have hh := hinput μ hμ n s (fun _ ↦ Set.univ)
  simpa using hh

end SRWTightness
