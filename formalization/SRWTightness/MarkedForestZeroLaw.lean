import SRWTightness.MarkedTreeBranchingLaw
import SRWTightness.ExternalMarkedGWForestJoint

open MeasureTheory
open scoped ENNReal
set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.FiniteExcursionRecord
set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.GeometricGWRecord

namespace SRWTightness

local instance markedForestZeroNatListMeasurable :
    MeasurableSpace (List ℕ) := ⊤
local instance markedForestZeroNatListSingleton :
    MeasurableSingletonClass (List ℕ) := ⟨fun _ ↦ trivial⟩

/-- At depth zero the aggregate population is precisely the number of ordered roots. -/
theorem forest_population_list_zero {M : Type*} (rs : List M) :
    forestPopulationList 0 rs = [rs.length] := by
  simp [forestPopulationList, forestLevelPopulation, finiteRecordLevelPopulation,
    List.ofFn_succ]

/-- Flattening zero-depth leaf records preserves the original ordered mark list. -/
theorem forest_leaves_zero {M : Type*} (rs : List M) :
    rs.flatMap (finiteRecordLeaves 0) = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [finiteRecordLeaves, ih]

/-- The literal forest joint-law identity is internal at depth zero, for every root count. -/
theorem marked_forest_joint_zero_internal {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ]
    (k : ℕ) (s : Set GeometricGWRecord) (E : GeometricGWRecord → Set (List M)) :
    independentForestLaw (finiteRecordReferenceMeasure μ 0) k
      {rs | forestPopulationList 0 rs ∈ s ∧
        rs.flatMap (finiteRecordLeaves 0) ∈ E (forestPopulationList 0 rs)} =
      ∫⁻ g in s, independentForestLaw μ (geometricGWPopulation g 0) (E g)
        ∂geometricGWRecordLaw k 0 := by
  classical
  rw [finite_record_reference_measure_zero]
  have hleaf : (finiteRecordLeaves 0 : M → List M) = fun x ↦ [x] := rfl
  simp_rw [forest_population_list_zero, hleaf]
  have hflat (rs : List M) : rs.flatMap (fun x ↦ [x]) = rs := by simp
  simp_rw [hflat]
  have hr : geometricGWRecordLaw k 0 = Measure.dirac (α := GeometricGWRecord) [k] := rfl
  rw [hr, restrict_dirac]
  by_cases hk : [k] ∈ s
  · rw [if_pos hk, lintegral_dirac]
    have hpop : geometricGWPopulation [k] 0 = k := by simp [geometricGWPopulation]
    rw [hpop]
    unfold independentForestLaw
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
      Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    simp only [Set.preimage_setOf_eq, List.length_ofFn, hk, true_and]
    rfl
  · rw [if_neg hk, lintegral_zero_measure]
    rw [independentForestLaw, Measure.map_apply (measurable_of_countable _)
      (Set.to_countable _).measurableSet]
    simp [List.length_ofFn, hk]

end SRWTightness
