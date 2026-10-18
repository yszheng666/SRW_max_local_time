import SRWTightness.GeometricMarkedListJoint
import SRWTightness.GeometricGWOneGeneration

open MeasureTheory
open scoped ENNReal
set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.FiniteExcursionRecord SRWTightness.GeometricGWRecord

namespace SRWTightness

attribute [local instance] geometricGWOneNatListMeasurable geometricGWOneNatListSingleton

/-- The single-root one-generation record stores the terminal count and then its one root. -/
theorem finite_record_population_list_one {M : Type*} (rs : List M) :
    finiteRecordPopulationList 1 rs = [rs.length, 1] := by
  simp [finiteRecordPopulationList, List.ofFn_succ, finiteRecordLevelPopulation]

/-- One-generation terminal leaves are the original ordered child marks. -/
theorem finite_record_leaves_one {M : Type*} (rs : List M) : finiteRecordLeaves 1 rs = rs := by
  change rs.flatMap (fun x ↦ [x]) = rs
  simp

/-- The original marked GW joint identity is internal at one generation, for arbitrary events. -/
theorem marked_tree_joint_one_internal {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ]
    (s : Set GeometricGWRecord) (E : GeometricGWRecord → Set (List M)) :
    finiteRecordReferenceMass μ 1 {r | finiteRecordPopulationList 1 r ∈ s ∧
      finiteRecordLeaves 1 r ∈ E (finiteRecordPopulationList 1 r)} =
      ∫⁻ g in s, independentForestLaw μ (geometricGWPopulation g 1) (E g)
        ∂geometricGWRecordLaw 1 1 := by
  rw [← finiteRecordReferenceMeasure_apply, finite_record_reference_measure_successor,
    finite_record_reference_measure_zero]
  simp_rw [finite_record_population_list_one, finite_record_leaves_one]
  rw [geometric_gw_record_one_generation,
    setLIntegral_map (Set.to_countable s).measurableSet (measurable_of_countable _)
      (measurable_of_countable _)]
  have hpop (j : ℕ) : geometricGWPopulation [j, 1] 1 = j := by
    simp [geometricGWPopulation]
  simp_rw [hpop]
  exact geometric_marked_list_joint_law μ {j | [j, 1] ∈ s} (fun j ↦ E [j, 1])

end SRWTightness
