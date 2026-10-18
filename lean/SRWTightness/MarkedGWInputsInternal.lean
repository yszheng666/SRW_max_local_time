import SRWTightness.MarkedForestJointInternal
import SRWTightness.ForestPopulationSingleton
import SRWTightness.IndependentForestSingleton

open MeasureTheory
set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.FiniteExcursionRecord SRWTightness.GeometricGWRecord

namespace SRWTightness

attribute [local instance] geometricGWOneNatListMeasurable geometricGWOneNatListSingleton

/-- The entire original single-root marked GW joint input is internally inhabited. -/
theorem marked_gw_joint_input_internal {M : Type*} [mM : MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [mLM : MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] : MarkedGWJointInput M := by
  have hmM : mM = ⊤ := countable_measurable_space_top M
  have hmLM : mLM = ⊤ := countable_measurable_space_top (List M)
  subst mM
  subst mLM
  letI : MeasurableSpace M := ⊤
  letI : MeasurableSpace (List M) := ⊤
  intro μ hμ n s E
  letI := hμ
  letI := finiteExcursionRecord_countable M n
  letI : MeasurableSpace (FiniteExcursionRecord M n) := ⊤
  letI : MeasurableSingletonClass (FiniteExcursionRecord M n) := ⟨fun _ ↦ trivial⟩
  letI : MeasurableSpace (List (FiniteExcursionRecord M n)) := ⊤
  letI : MeasurableSingletonClass (List (FiniteExcursionRecord M n)) := ⟨fun _ ↦ trivial⟩
  letI := finite_record_reference_measure_probability_internal μ n
  have hh := marked_forest_joint_internal μ n 1 s E
  rw [independent_forest_singleton_law,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    finiteRecordReferenceMeasure_apply] at hh
  simpa only [Set.preimage_setOf_eq, forest_population_list_singleton,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] using hh

/-- The entire original independent marked forest joint input is internally inhabited. -/
theorem marked_gw_forest_joint_input_internal {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] : MarkedGWForestJointInput M := by
  refine ⟨marked_gw_joint_input_internal, ?_⟩
  intro μ hμ n k mR hR mLR hLR s E
  letI := hμ
  exact marked_forest_joint_internal μ n k s E

/-- The original population-only marked tree input follows internally from its full joint law. -/
theorem marked_gw_tree_input_internal {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] : MarkedGWTreeInput M := by
  letI : MeasurableSpace (List M) := ⊤
  letI : MeasurableSingletonClass (List M) := ⟨fun _ ↦ trivial⟩
  exact markedGWJoint_population marked_gw_joint_input_internal

end SRWTightness
