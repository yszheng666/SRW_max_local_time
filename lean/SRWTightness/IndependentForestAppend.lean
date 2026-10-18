import SRWTightness.IndependentForestMap

open MeasureTheory

namespace SRWTightness

/-- Concatenating independent coordinate blocks gives the ordinary independent product array. -/
theorem independent_array_append_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (μ : Measure M) [IsProbabilityMeasure μ]
    (k l : ℕ) :
    ((Measure.pi (fun _ : Fin k ↦ μ)).prod (Measure.pi (fun _ : Fin l ↦ μ))).map
      (fun q ↦ Fin.append q.1 q.2) = Measure.pi (fun _ : Fin (k + l) ↦ μ) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l ↦ M)
  let d := MeasurableEquiv.piCongrLeft (fun _ : Fin (k + l) ↦ M) finSumFinEquiv
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin k ⊕ Fin l ↦ μ)
  have hd := measurePreserving_piCongrLeft (fun _ : Fin (k + l) ↦ μ) finSumFinEquiv
  have hh := hd.comp he
  have hf : (fun q : (Fin k → M) × (Fin l → M) ↦ Fin.append q.1 q.2) =
      d ∘ e.symm := by
    funext q i
    dsimp [d, e, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft, Fin.append, finSumFinEquiv]
    refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i <;> simp
  rw [hf]
  exact hh.map_eq

/-- Appending two independent ordered root lists gives the exact larger independent forest. -/
theorem independent_forest_append_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ] (k l : ℕ) :
    ((independentForestLaw μ k).prod (independentForestLaw μ l)).map
      (fun q ↦ q.1 ++ q.2) = independentForestLaw μ (k + l) := by
  unfold independentForestLaw
  rw [Measure.map_prod_map _ _ (measurable_of_countable _)
    (measurable_of_countable _)]
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hf : (fun q : (Fin k → M) × (Fin l → M) ↦ List.ofFn q.1 ++ List.ofFn q.2) =
      List.ofFn ∘ (fun q ↦ Fin.append q.1 q.2) := by
    funext q
    exact (List.ofFn_fin_append q.1 q.2).symm
  change ((Measure.pi (fun _ : Fin k ↦ μ)).prod
    (Measure.pi (fun _ : Fin l ↦ μ))).map (fun q : (Fin k → M) × (Fin l → M) ↦
    List.ofFn q.1 ++ List.ofFn q.2) = _
  rw [hf, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    independent_array_append_law]

end SRWTightness
