import SRWTightness.IndependentForestLaw
import SRWTightness.MarkSumGenerating

open MeasureTheory

namespace SRWTightness

/-- An occupation event in an independent mark list has exactly the finite-product probability. -/
theorem mark_list_product_probability (D K : Finset Site) (α : ℝ) (k h : ℕ)
    [MeasurableSpace (List (Mark K))] [MeasurableSingletonClass (List (Mark K))] :
    independentForestLaw (referenceMarkLaw D K α) k
      {vs | ∃ y : K, h ≤ (vs.map (fun v ↦ v y)).sum} =
      markProductLaw D K α k {Y | ∃ y : K, h ≤ sumMarks K k Y y} := by
  rw [independentForestLaw, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  congr 1
  ext Y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, List.map_ofFn, List.sum_ofFn, sumMarks,
    Function.comp_def]

/-- Translating the whole observation set preserves its existential occupation event. -/
theorem mark_product_translated_full_event (b : Site) (K : Finset Site) (k h : ℕ) :
    {Y : MarkSamples (translateFinset b K) k | ∃ z : K,
      h ≤ sumMarks (translateFinset b K) k Y
        ⟨b + z, (mem_translateFinset_add b K z).2 z.property⟩} =
      {Y | ∃ y : translateFinset b K, h ≤ sumMarks (translateFinset b K) k Y y} := by
  ext Y
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨⟨b + z, (mem_translateFinset_add b K z).2 z.property⟩, hz⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp y.property
    refine ⟨⟨z, hz⟩, ?_⟩
    have heq : (⟨b + z, (mem_translateFinset_add b K z).2 hz⟩ : translateFinset b K) = y :=
      Subtype.ext he
    simpa only [heq] using hy

end SRWTightness
