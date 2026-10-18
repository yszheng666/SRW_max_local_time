import SRWTightness.ExternalMarkedGWJoint
import SRWTightness.FiniteRecordReferenceMeasure
import SRWTightness.ForestPopulationError

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- Aggregate forest populations, terminal generation first as in the existing GW record law. -/
def forestPopulationList {M : Type*} (n : ℕ) (rs : List (FiniteExcursionRecord M n)) :
    GeometricGWRecord := List.ofFn (fun j : Fin (n + 1) ↦ forestLevelPopulation n rs j)

/-- Standard marked GW branching law for any fixed number of independent roots. The single-root
field retains the already used normalization input; the forest field gives aggregate populations
and independent terminal marks, without source events, geometry or comparison estimates. -/
structure MarkedGWForestJointInput (M : Type*) [MeasurableSpace M] [MeasurableSingletonClass M]
    [Countable M] [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)] : Prop where
  singleRoot : MarkedGWJointInput M
  forest : ∀ μ : Measure M, IsProbabilityMeasure μ → ∀ (n k : ℕ)
    [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)]
    [MeasurableSpace (List (FiniteExcursionRecord M n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord M n))]
    (s : Set GeometricGWRecord) (E : GeometricGWRecord → Set (List M)),
    independentForestLaw (finiteRecordReferenceMeasure μ n) k
      {rs | forestPopulationList n rs ∈ s ∧
        rs.flatMap (finiteRecordLeaves n) ∈ E (forestPopulationList n rs)} =
      ∫⁻ g in s, independentForestLaw μ (geometricGWPopulation g n) (E g)
        ∂geometricGWRecordLaw k n

end SRWTightness
