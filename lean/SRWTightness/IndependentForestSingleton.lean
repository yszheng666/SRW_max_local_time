import SRWTightness.IndependentForestMap

open MeasureTheory

namespace SRWTightness

/-- A one-root independent forest is exactly the mark law mapped to a singleton list. -/
theorem independent_forest_singleton_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ] :
    independentForestLaw μ 1 = μ.map (fun x ↦ [x]) := by
  unfold independentForestLaw
  have hf : (List.ofFn : (Fin 1 → M) → List M) =
      (fun x ↦ [x]) ∘ Function.eval (0 : Fin 1) := by
    funext ξ
    simp [List.ofFn_succ]
  rw [hf, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    (measurePreserving_eval (fun _ : Fin 1 ↦ μ) 0).map_eq]

end SRWTightness
