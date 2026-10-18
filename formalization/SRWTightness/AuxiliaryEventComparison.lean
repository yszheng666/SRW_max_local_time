import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.Basic

open MeasureTheory

namespace SRWTightness

/-- Event probabilities in a finite product are integrals of the section probabilities. -/
theorem product_event_section_data {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : Set (Ω × Ξ)) (hs : MeasurableSet s) :
    Integrable (fun y ↦ μ.real ((fun x ↦ (x, y)) ⁻¹' s)) ν ∧
    (μ.prod ν).real s = ∫ y, μ.real ((fun x ↦ (x, y)) ⁻¹' s) ∂ν := by
  classical
  let f : Ω × Ξ → ℝ := s.indicator (fun _ ↦ 1)
  have hf : Integrable f (μ.prod ν) := (integrable_const 1).indicator hs
  have he (y : Ξ) : (∫ x, f (x, y) ∂μ) = μ.real ((fun x ↦ (x, y)) ⁻¹' s) := by
    simpa only [f, Set.indicator, Set.mem_preimage, Pi.one_apply] using
      (integral_indicator_one (μ := μ) (measurable_prodMk_right hs))
  refine ⟨?_, ?_⟩
  · simpa only [he] using hf.integral_prod_right
  · have hh := integral_prod_symm f hf
    simp_rw [he] at hh
    have hi : (∫ z, f z ∂μ.prod ν) = (μ.prod ν).real s :=
      integral_indicator_one (μ := μ.prod ν) hs
    exact hi.symm.trans hh

/-- A uniform section error remains unchanged after integrating an independent probability space. -/
theorem auxiliary_event_comparison {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ κ : Measure Ω) (ν : Measure Ξ) [IsFiniteMeasure μ] [IsFiniteMeasure κ]
    [IsProbabilityMeasure ν] (δ : ℝ) (s : Set (Ω × Ξ)) (hs : MeasurableSet s)
    (hsection : ∀ᵐ y ∂ν,
      |μ.real ((fun x ↦ (x, y)) ⁻¹' s) - κ.real ((fun x ↦ (x, y)) ⁻¹' s)| ≤ δ) :
    |(μ.prod ν).real s - (κ.prod ν).real s| ≤ δ := by
  obtain ⟨hμ, eμ⟩ := product_event_section_data μ ν s hs
  obtain ⟨hκ, eκ⟩ := product_event_section_data κ ν s hs
  rw [eμ, eκ, ← integral_sub hμ hκ]
  calc
    _ ≤ ∫ y, |μ.real ((fun x ↦ (x, y)) ⁻¹' s) -
        κ.real ((fun x ↦ (x, y)) ⁻¹' s)| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Ξ, δ ∂ν := integral_mono_ae (hμ.sub hκ).abs (integrable_const δ) hsection
    _ = δ := by simp

/-- A convex-event comparison extends to measurable events with almost surely convex sections. -/
theorem convex_event_comparison_aux {E Ξ : Type*} [AddCommMonoid E] [Module ℝ E]
    [MeasurableSpace E] [MeasurableSpace Ξ]
    (μ κ : Measure E) (ν : Measure Ξ) [IsFiniteMeasure μ] [IsFiniteMeasure κ]
    [IsProbabilityMeasure ν] (δ : ℝ)
    (hconvex : ∀ s : Set E, MeasurableSet s → Convex ℝ s → |μ.real s - κ.real s| ≤ δ)
    (s : Set (E × Ξ)) (hs : MeasurableSet s)
    (hsections : ∀ᵐ y ∂ν, Convex ℝ ((fun x ↦ (x, y)) ⁻¹' s)) :
    |(μ.prod ν).real s - (κ.prod ν).real s| ≤ δ := by
  apply auxiliary_event_comparison μ κ ν δ s hs
  filter_upwards [hsections] with y hy
  exact hconvex _ (measurable_prodMk_right hs) hy

end SRWTightness
