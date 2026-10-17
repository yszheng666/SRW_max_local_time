import SRWTightness.ExternalGaussianWindow

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- Uniform conditional-section probability bounds transfer to an event with an independent factor. -/
theorem product_event_section_bounds {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (s : Set Ω) (E : Set (Ω × Ξ)) (c : ℝ≥0∞)
    (hs : MeasurableSet s) (hE : MeasurableSet E) (hsub : E ⊆ s ×ˢ Set.univ)
    (hsection : ∀ x ∈ s, c ≤ ν (Prod.mk x ⁻¹' E)) :
    c * μ s ≤ (μ.prod ν) E ∧ (μ.prod ν) E ≤ μ s := by
  constructor
  · rw [Measure.prod_apply hE]
    calc
      c * μ s = ∫⁻ x, s.indicator (fun _ ↦ c) x ∂μ :=
        (lintegral_indicator_const hs c).symm
      _ ≤ _ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ s
        · simpa only [Set.indicator_of_mem hx] using hsection x hx
        · simp only [Set.indicator_of_notMem hx]
          exact zero_le
  · calc
      _ ≤ (μ.prod ν) (s ×ˢ Set.univ) := measure_mono hsub
      _ = _ := by rw [Measure.prod_prod, measure_univ, mul_one]

/-- An upper bound on every section yields the corresponding multiplicative event upper bound. -/
theorem product_event_section_upper {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (s : Set Ω) (E : Set (Ω × Ξ)) (C : ℝ≥0∞)
    (hs : MeasurableSet s) (hE : MeasurableSet E) (hsub : E ⊆ s ×ˢ Set.univ)
    (hsection : ∀ x ∈ s, ν (Prod.mk x ⁻¹' E) ≤ C) :
    (μ.prod ν) E ≤ C * μ s := by
  rw [Measure.prod_apply hE, ← lintegral_indicator_const hs C]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ s
  · simpa only [Set.indicator_of_mem hx] using hsection x hx
  · have he : Prod.mk x ⁻¹' E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hx (hsub hy).1
    simp only [he, measure_empty, Set.indicator_of_notMem hx, le_refl]

end SRWTightness
