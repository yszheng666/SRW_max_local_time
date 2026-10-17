import SRWTightness.MarkedTreeBranchingLaw
import SRWTightness.ExternalMarkedGWJoint

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

attribute [local instance] Classical.propDecidable

/-- A fixed-size independent forest has deterministic length. -/
theorem independent_forest_length_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ] (j : ℕ) :
    (independentForestLaw μ j).map List.length = Measure.dirac j := by
  rw [independentForestLaw, Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)]
  have hf : (List.length ∘ (List.ofFn : (Fin j → M) → List M)) = fun _ ↦ j := by
    funext f
    exact List.length_ofFn
  rw [hf, Measure.map_const, measure_univ, one_smul]

/-- The child count of the constructed marked branching law is exactly geometric. -/
theorem geometric_marked_list_length_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ] :
    (geometricMarkedListLaw μ).map List.length = geometricGWOffspringLaw := by
  rw [geometricMarkedListLaw, Measure.map_sum (measurable_of_countable _).aemeasurable]
  simp only [Measure.map_smul, independent_forest_length_law]
  exact Measure.sum_smul_dirac geometricGWOffspringLaw

/-- Every event of a fixed-size forest can be intersected with its deterministic length. -/
theorem independent_forest_length_event {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ]
    (j : ℕ) (s : Set ℕ) (E : ℕ → Set (List M)) :
    independentForestLaw μ j {rs | rs.length ∈ s ∧ rs ∈ E rs.length} =
      if j ∈ s then independentForestLaw μ j (E j) else 0 := by
  classical
  rw [independentForestLaw, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  simp only [Set.preimage_setOf_eq, List.length_ofFn]
  by_cases hj : j ∈ s
  · simp only [hj, true_and, if_pos]
    rw [Measure.map_apply (measurable_of_countable _)
      (Set.to_countable _).measurableSet]
    rfl
  · simp [hj]

/-- The full count/ordered-mark joint law, with an arbitrary count-dependent mark event. -/
theorem geometric_marked_list_joint_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ]
    (s : Set ℕ) (E : ℕ → Set (List M)) :
    geometricMarkedListLaw μ {rs | rs.length ∈ s ∧ rs ∈ E rs.length} =
      ∫⁻ j in s, independentForestLaw μ j (E j) ∂geometricGWOffspringLaw := by
  classical
  rw [geometricMarkedListLaw, Measure.sum_apply _ (Set.to_countable _).measurableSet]
  simp only [Measure.smul_apply, smul_eq_mul, independent_forest_length_event]
  conv_rhs =>
    rw [← Measure.sum_smul_dirac geometricGWOffspringLaw,
      Measure.restrict_sum _ (Set.to_countable s).measurableSet, lintegral_sum_measure]
  apply tsum_congr
  intro j
  rw [Measure.restrict_smul, lintegral_smul_measure]
  by_cases hj : j ∈ s <;> simp [hj, restrict_dirac, lintegral_dirac, smul_eq_mul]

end SRWTightness
