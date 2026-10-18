import SRWTightness.MarkedForestJointInternal
import SRWTightness.ReferenceWordMark

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- The ordered reference forest has the exact GW population and independent terminal-word law. -/
theorem ordered_reference_forest_joint (D K : Finset Site) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    [MeasurableSpace (List WordMark)] [MeasurableSingletonClass (List WordMark)]
    (n k : ℕ) [MeasurableSpace (FiniteExcursionRecord WordMark n)]
    [MeasurableSingletonClass (FiniteExcursionRecord WordMark n)]
    [MeasurableSpace (List (FiniteExcursionRecord WordMark n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark n))]
    (s : Set GeometricGWRecord) (E : GeometricGWRecord → Set (List WordMark)) :
    independentForestLaw (finiteRecordReferenceMeasure (referenceWordMarkLaw D K α) n) k
      {rs | forestPopulationList n rs ∈ s ∧
        rs.flatMap (finiteRecordLeaves n) ∈ E (forestPopulationList n rs)} =
      ∫⁻ g in s, independentForestLaw (referenceWordMarkLaw D K α)
        (geometricGWPopulation g n) (E g) ∂geometricGWRecordLaw k n := by
  letI := referenceWordMarkLaw_probability D K α hα hcap
  exact marked_forest_joint_internal (referenceWordMarkLaw D K α) n k s E

end SRWTightness
