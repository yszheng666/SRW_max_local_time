import SRWTightness.GeometricCompoundForestFlatten
import SRWTightness.GeometricGWFirstGenerationIntegral
import SRWTightness.IndependentForestFixedLengthEvent
import SRWTightness.ForestPopulationSuccessor
import SRWTightness.MarkedForestZeroLaw
import SRWTightness.CountableMeasurableSpaceTop

open MeasureTheory
open scoped ENNReal
set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.FiniteExcursionRecord SRWTightness.GeometricGWRecord

namespace SRWTightness

attribute [local instance] geometricGWOneNatListMeasurable geometricGWOneNatListSingleton

/-- The original marked forest joint identity holds internally at every depth and root count. -/
theorem marked_forest_joint_internal {M : Type*} [mM : MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [mLM : MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ] :
    ∀ (n k : ℕ) [mR : MeasurableSpace (FiniteExcursionRecord M n)]
      [MeasurableSingletonClass (FiniteExcursionRecord M n)]
      [mLR : MeasurableSpace (List (FiniteExcursionRecord M n))]
      [MeasurableSingletonClass (List (FiniteExcursionRecord M n))]
      (s : Set GeometricGWRecord) (E : GeometricGWRecord → Set (List M)),
      independentForestLaw (finiteRecordReferenceMeasure μ n) k
        {rs | forestPopulationList n rs ∈ s ∧
          rs.flatMap (finiteRecordLeaves n) ∈ E (forestPopulationList n rs)} =
        ∫⁻ g in s, independentForestLaw μ (geometricGWPopulation g n) (E g)
          ∂geometricGWRecordLaw k n := by
  have hmM : mM = ⊤ := countable_measurable_space_top M
  have hmLM : mLM = ⊤ := countable_measurable_space_top (List M)
  subst mM
  subst mLM
  letI : MeasurableSpace M := ⊤
  letI : MeasurableSpace (List M) := ⊤
  intro n
  induction n with
  | zero =>
    intro k mR hR mLR hLR s E
    letI := finiteExcursionRecord_countable M 0
    have hmR : mR = ⊤ := countable_measurable_space_top (FiniteExcursionRecord M 0)
    have hmLR : mLR = ⊤ := countable_measurable_space_top (List (FiniteExcursionRecord M 0))
    subst mR
    subst mLR
    exact marked_forest_joint_zero_internal μ k s E
  | succ n ih =>
    intro k mR hR mLR hLR s E
    letI := finiteExcursionRecord_countable M (n + 1)
    have hmR : mR = ⊤ := countable_measurable_space_top (FiniteExcursionRecord M (n + 1))
    have hmLR : mLR = ⊤ :=
      countable_measurable_space_top (List (FiniteExcursionRecord M (n + 1)))
    subst mR
    subst mLR
    letI := finiteExcursionRecord_countable M n
    letI : MeasurableSpace (FiniteExcursionRecord M n) := ⊤
    letI : MeasurableSingletonClass (FiniteExcursionRecord M n) := ⟨fun _ ↦ trivial⟩
    letI : MeasurableSpace (List (FiniteExcursionRecord M n)) := ⊤
    letI : MeasurableSingletonClass (List (FiniteExcursionRecord M n)) := ⟨fun _ ↦ trivial⟩
    letI : MeasurableSpace (List (List (FiniteExcursionRecord M n))) := ⊤
    letI : MeasurableSingletonClass (List (List (FiniteExcursionRecord M n))) :=
      ⟨fun _ ↦ trivial⟩
    letI := finite_record_reference_measure_probability_internal μ n
    rw [finite_record_reference_measure_successor]
    simp_rw [forest_population_list_successor n]
    have hleaves (rss : List (List (FiniteExcursionRecord M n))) :=
      forest_leaves_successor n rss
    simp_rw [hleaves]
    let Q (j : ℕ) : Set (List (List (FiniteExcursionRecord M n))) :=
      {rss | forestPopulationList n rss.flatten ++ [j] ∈ s ∧
        rss.flatten.flatMap (finiteRecordLeaves n) ∈
          E (forestPopulationList n rss.flatten ++ [j])}
    change independentForestLaw (geometricMarkedListLaw (finiteRecordReferenceMeasure μ n)) k
      {rss | rss ∈ Q rss.length} = _
    rw [independent_forest_fixed_length_event]
    let T : Set (List (FiniteExcursionRecord M n)) :=
      {rs | forestPopulationList n rs ++ [k] ∈ s ∧
        rs.flatMap (finiteRecordLeaves n) ∈ E (forestPopulationList n rs ++ [k])}
    change independentForestLaw (geometricMarkedListLaw (finiteRecordReferenceMeasure μ n)) k
      (List.flatten ⁻¹' T) = _
    rw [← Measure.map_apply (measurable_of_countable _) (Set.to_countable T).measurableSet,
      geometric_compound_forest_flatten,
      Measure.bind_apply (Set.to_countable T).measurableSet
        (measurable_of_countable _).aemeasurable,
      geometric_gw_first_generation_set_integral]
    simp_rw [geometric_gw_population_append]
    apply lintegral_congr_ae
    apply Filter.Eventually.of_forall
    intro j
    dsimp only [T]
    exact ih j {g | g ++ [k] ∈ s} (fun g ↦ E (g ++ [k]))

end SRWTightness
