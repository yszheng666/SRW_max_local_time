import SRWTightness.IndependentForestLaw

open MeasureTheory

namespace SRWTightness

/-- Mapping every ordered root commutes with the independent forest construction. -/
theorem independent_forest_map {M N : Type*} [MeasurableSpace M] [MeasurableSpace N]
    [MeasurableSingletonClass M] [MeasurableSingletonClass N] [Countable M] [Countable N]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)]
    [MeasurableSpace (List N)] [MeasurableSingletonClass (List N)]
    (μ : Measure M) [IsProbabilityMeasure μ] (f : M → N) (j : ℕ) :
    (independentForestLaw μ j).map (List.map f) = independentForestLaw (μ.map f) j := by
  letI : IsProbabilityMeasure (μ.map f) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  rw [independentForestLaw, Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)]
  have hf : (List.map f ∘ (List.ofFn : (Fin j → M) → List M)) =
      List.ofFn ∘ (fun x : Fin j → M ↦ fun i ↦ f (x i)) := by
    funext x
    simp only [Function.comp_apply, List.map_ofFn, Function.comp_def]
  rw [hf, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rw [Measure.pi_map_pi (fun _ ↦ (measurable_of_countable f).aemeasurable)]
  rfl

end SRWTightness
