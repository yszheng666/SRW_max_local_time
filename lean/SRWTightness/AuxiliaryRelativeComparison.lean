import SRWTightness.AuxiliaryEventComparison

open MeasureTheory

namespace SRWTightness

/-- Uniform relative record bounds persist after integrating the same independent auxiliary law. -/
theorem auxiliary_relative_comparison {Ω Γ Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace Ξ]
    (μ : Measure Ω) (κ : Measure Γ) (ν : Measure Ξ)
    [IsFiniteMeasure μ] [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (c C : ℝ) (s : Set (Ω × Ξ)) (t : Set (Γ × Ξ))
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsection : ∀ᵐ y ∂ν,
      c * κ.real ((fun x ↦ (x, y)) ⁻¹' t) ≤ μ.real ((fun x ↦ (x, y)) ⁻¹' s) ∧
      μ.real ((fun x ↦ (x, y)) ⁻¹' s) ≤ C * κ.real ((fun x ↦ (x, y)) ⁻¹' t)) :
    c * (κ.prod ν).real t ≤ (μ.prod ν).real s ∧
      (μ.prod ν).real s ≤ C * (κ.prod ν).real t := by
  obtain ⟨hμ, eμ⟩ := product_event_section_data μ ν s hs
  obtain ⟨hκ, eκ⟩ := product_event_section_data κ ν t ht
  rw [eμ, eκ, ← integral_const_mul, ← integral_const_mul]
  exact ⟨integral_mono_ae (hκ.const_mul c) hμ (hsection.mono fun _ h ↦ h.1),
    integral_mono_ae hμ (hκ.const_mul C) (hsection.mono fun _ h ↦ h.2)⟩

end SRWTightness
