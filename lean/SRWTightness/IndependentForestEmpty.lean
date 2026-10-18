import SRWTightness.IndependentForestLaw

open MeasureTheory

namespace SRWTightness

/-- Zero independent roots give the empty ordered forest with probability one. -/
theorem independent_forest_empty_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ] :
    independentForestLaw μ 0 = Measure.dirac [] := by
  unfold independentForestLaw
  have hf : (List.ofFn : (Fin 0 → M) → List M) = fun _ ↦ [] := by
    funext ξ
    simp
  rw [hf, Measure.map_const, measure_univ, one_smul]

end SRWTightness
