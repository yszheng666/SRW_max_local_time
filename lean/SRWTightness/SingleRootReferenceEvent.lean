import SRWTightness.IndependentForestLaw

open MeasureTheory

namespace SRWTightness

/-- A singleton-root forest event has exactly the corresponding one-tree probability. -/
theorem independentForestLaw_single_root_event {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ]
    (s : Set M) :
    independentForestLaw μ 1 {rs | ∃ r ∈ s, rs = [r]} = μ s := by
  rw [independentForestLaw, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  have he : List.ofFn ⁻¹' {rs | ∃ r ∈ s, rs = [r]} =
      (fun f : Fin 1 → M ↦ f 0) ⁻¹' s := by
    ext f
    simp [List.ofFn_succ]
  rw [he]
  exact (measurePreserving_eval (fun _ : Fin 1 ↦ μ) 0).measure_preimage
    (Set.to_countable s).measurableSet.nullMeasurableSet

end SRWTightness
