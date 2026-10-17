import SRWTightness.ProductEventSectionBounds

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- Real-valued two-sided section bounds integrate with the endpoint-event probability. -/
theorem product_event_real_bounds {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set Ω) (E : Set (Ω × Ξ)) (c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hs : MeasurableSet s) (hE : MeasurableSet E) (hsub : E ⊆ s ×ˢ Set.univ)
    (hsection : ∀ x ∈ s, c ≤ ν.real (Prod.mk x ⁻¹' E) ∧
      ν.real (Prod.mk x ⁻¹' E) ≤ C) :
    c * μ.real s ≤ (μ.prod ν).real E ∧ (μ.prod ν).real E ≤ C * μ.real s := by
  have hl := (product_event_section_bounds μ ν s E (ENNReal.ofReal c) hs hE hsub
    (fun x hx ↦ (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
      (hsection x hx).1)).1
  have hu := product_event_section_upper μ ν s E (ENNReal.ofReal C) hs hE hsub
    (fun x hx ↦ (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hC).mpr
      (hsection x hx).2)
  have hlf := ENNReal.toReal_mono (measure_ne_top _ _) hl
  have huf := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hu
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hC,
    Measure.real] using And.intro hlf huf

end SRWTightness
