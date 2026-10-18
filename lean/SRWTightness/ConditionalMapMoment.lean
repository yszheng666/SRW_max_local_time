import SRWTightness.ConditionalMomentProduct

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Conditioning commutes with a measurable pushforward when the source event is its preimage. -/
theorem conditional_map_preimage {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (F : Ω → Ξ) (hF : Measurable F) (s : Set Ξ) (hs : MeasurableSet s) :
    (ProbabilityTheory.cond μ (F ⁻¹' s)).map F = ProbabilityTheory.cond (μ.map F) s := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, Measure.map_apply hF hs, Measure.restrict_map hF hs]

/-- A conditional moment on the pushforward law is exactly the composed source moment. -/
theorem conditional_map_moment {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (F : Ω → Ξ) (hF : Measurable F) (s : Set Ξ) (hs : MeasurableSet s)
    (f : Ξ → ℝ) (hf : Measurable f)
    (hi : Integrable f (ProbabilityTheory.cond (μ.map F) s)) :
    Integrable (fun x ↦ f (F x)) (ProbabilityTheory.cond μ (F ⁻¹' s)) ∧
      (∫ x, f (F x) ∂ProbabilityTheory.cond μ (F ⁻¹' s)) =
        ∫ y, f y ∂ProbabilityTheory.cond (μ.map F) s := by
  rw [← conditional_map_preimage μ F hF s hs] at hi ⊢
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hF.aemeasurable).mp hi, ?_⟩
  exact (integral_map hF.aemeasurable hf.aestronglyMeasurable).symm

end SRWTightness
