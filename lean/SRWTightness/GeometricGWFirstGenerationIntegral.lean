import SRWTightness.GeometricGWFirstGeneration

open MeasureTheory
open scoped ENNReal
set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.GeometricGWRecord

namespace SRWTightness

attribute [local instance] geometricGWOneNatListMeasurable geometricGWOneNatListSingleton

/-- Appending an initial population shifts chronological population coordinates by one. -/
theorem geometric_gw_population_append (g : GeometricGWRecord) (k n : ℕ) :
    geometricGWPopulation (g ++ [k]) (n + 1) = geometricGWPopulation g n := by
  simp [geometricGWPopulation, List.reverse_append]

/-- The exact first-generation recursion also holds for every nonnegative record event
functional. -/
theorem geometric_gw_first_generation_set_integral (k n : ℕ) (s : Set GeometricGWRecord)
    (F : GeometricGWRecord → ℝ≥0∞) :
    (∫⁻ g in s, F g ∂geometricGWRecordLaw k (n + 1)) =
      ∫⁻ j, ∫⁻ g in {g | g ++ [k] ∈ s}, F (g ++ [k])
        ∂geometricGWRecordLaw j n ∂geometricGWGenerationLaw k := by
  rw [← lintegral_indicator (Set.to_countable s).measurableSet,
    geometric_gw_record_first_generation,
    Measure.lintegral_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  apply lintegral_congr_ae
  apply Filter.Eventually.of_forall
  intro j
  dsimp only
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    ← lintegral_indicator (Set.to_countable _).measurableSet]
  apply lintegral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  by_cases hg : g ++ [k] ∈ s <;> simp [Set.indicator_apply, hg]

end SRWTightness
