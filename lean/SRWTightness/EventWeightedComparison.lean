import SRWTightness.OrderedWordMomentComparison

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Event comparison on a selected region dominates the restricted pushforward measure. -/
theorem restricted_map_le_of_event_comparison {Ω R : Type*}
    [MeasurableSpace Ω] [MeasurableSpace R] (μ : Measure Ω) (ν : Measure R)
    (F : Ω → R) (hF : Measurable F) (A : Set R) (hA : MeasurableSet A) (c : ℝ≥0∞)
    (hc : ∀ s : Set R, MeasurableSet s → s ⊆ A → μ (F ⁻¹' s) ≤ c * ν s) :
    (μ.map F).restrict A ≤ c • ν.restrict A := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.restrict_apply hs, Measure.map_apply hF (hs.inter hA),
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs]
  exact hc (s ∩ A) (hs.inter hA) Set.inter_subset_right

/-- The event comparison bounds measurable nonnegative tests
without integrability assumptions. -/
theorem restricted_lintegral_le_of_event_comparison {Ω R : Type*}
    [MeasurableSpace Ω] [MeasurableSpace R] (μ : Measure Ω) (ν : Measure R)
    (F : Ω → R) (hF : Measurable F) (A : Set R) (hA : MeasurableSet A) (c : ℝ≥0∞)
    (hc : ∀ s : Set R, MeasurableSet s → s ⊆ A → μ (F ⁻¹' s) ≤ c * ν s)
    (f : R → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω in F ⁻¹' A, f (F ω) ∂μ) ≤ c * ∫⁻ r in A, f r ∂ν := by
  rw [← setLIntegral_map hA hf hF]
  have hh := lintegral_mono'
    (restricted_map_le_of_event_comparison μ ν F hF A hA c hc) (le_refl f)
  simpa only [lintegral_smul_measure, smul_eq_mul] using hh

end SRWTightness
