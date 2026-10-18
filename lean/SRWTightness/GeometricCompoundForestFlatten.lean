import SRWTightness.GeometricForestBindConvolution
import SRWTightness.IndependentForestCons
import SRWTightness.IndependentForestEmpty
import SRWTightness.GeometricGWGenerationCons

open MeasureTheory

namespace SRWTightness

/-- Flattening independent geometric marked parents gives the exact GW-count child-forest
mixture. -/
theorem geometric_compound_forest_flatten {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] [MeasurableSpace (List (List M))]
    [MeasurableSingletonClass (List (List M))]
    (μ : Measure M) [IsProbabilityMeasure μ] (k : ℕ) :
    (independentForestLaw (geometricMarkedListLaw μ) k).map List.flatten =
      (geometricGWGenerationLaw k).bind (independentForestLaw μ) := by
  induction k with
  | zero =>
    rw [independent_forest_empty_law, Measure.map_dirac' (measurable_of_countable _),
      geometric_gw_generation_zero, Measure.dirac_bind (measurable_of_countable _) 0,
      independent_forest_empty_law]
    rfl
  | succ k ih =>
    rw [independent_forest_cons_law,
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    have hf : (List.flatten ∘ (fun q : List M × List (List M) ↦ q.1 :: q.2)) =
        (fun q : List M × List M ↦ q.1 ++ q.2) ∘ (fun q ↦ (q.1, q.2.flatten)) := rfl
    rw [hf, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    have hm : ((geometricMarkedListLaw μ).prod
        (independentForestLaw (geometricMarkedListLaw μ) k)).map
          (fun q ↦ (q.1, q.2.flatten)) =
        (geometricMarkedListLaw μ).prod
          ((independentForestLaw (geometricMarkedListLaw μ) k).map List.flatten) := by
      simpa only [Measure.map_id, Prod.map_def, id_eq] using
        (Measure.map_prod_map (geometricMarkedListLaw μ)
          (independentForestLaw (geometricMarkedListLaw μ) k) measurable_id
          (measurable_of_countable List.flatten)).symm
    rw [hm, ih, geometric_forest_bind_convolution, geometric_gw_generation_cons,
      measure_map_bind_input _ _ _ (measurable_of_countable _) (measurable_of_countable _)]

end SRWTightness
