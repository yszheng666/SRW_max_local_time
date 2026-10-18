import SRWTightness.ReferenceMarkTranslation

open MeasureTheory

namespace SRWTightness

/-- Pulling back each translated independent mark gives the original full product law. -/
theorem markProductLaw_translate_pullback (b : Site) (D K : Finset Site) (α : ℝ) (k : ℕ) :
    (markProductLaw (translateFinset b D) (translateFinset b K) α k).map
      (fun Y i ↦ translatedMarkPullback b K (Y i)) = markProductLaw D K α k := by
  letI := referenceMarkLaw_finite D K α
  letI : IsFiniteMeasure
      ((referenceMarkLaw (translateFinset b D) (translateFinset b K) α).map
        (translatedMarkPullback b K)) := by
    rw [referenceMarkLaw_translate_pullback]
    infer_instance
  rw [markProductLaw, Measure.pi_map_pi
    (fun _ ↦ (measurable_translatedMarkPullback b K).aemeasurable)]
  simp only [referenceMarkLaw_translate_pullback, markProductLaw]

/-- The entire original projected reference-mark translation interface is internal. -/
theorem projected_mark_translation_input_internal : ProjectedMarkTranslationInput := by
  intro b D A K hAK α k a
  let f : MarkSamples (translateFinset b K) k → MarkSamples K k :=
    fun Y i ↦ translatedMarkPullback b K (Y i)
  let s : Set (MarkSamples K k) :=
    {Y | ∃ z : A, a ≤ sumMarks K k Y ⟨z, hAK z.property⟩}
  have hf : Measurable f := measurable_pi_lambda _
    (fun i ↦ (measurable_translatedMarkPullback b K).comp (measurable_pi_apply i))
  have hs : MeasurableSet s := (Set.to_countable s).measurableSet
  have he : {Y : MarkSamples (translateFinset b K) k | ∃ z : A,
      a ≤ sumMarks (translateFinset b K) k Y
        ⟨b + z, (mem_translateFinset_add b K z).mpr (hAK z.property)⟩} = f ⁻¹' s := rfl
  simp only [measureReal_def]
  rw [he, ← Measure.map_apply hf hs, markProductLaw_translate_pullback]

end SRWTightness
