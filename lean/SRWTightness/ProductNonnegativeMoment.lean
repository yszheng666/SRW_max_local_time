import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace SRWTightness

/-- Uniform nonnegative section moments ensure product integrability and allow endpoint integration. -/
theorem product_nonnegative_moment {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω × Ξ → ℝ) (hf : StronglyMeasurable f) (hn : ∀ p, 0 ≤ f p)
    (C : ℝ) (hsection : ∀ x, Integrable (fun y ↦ f (x, y)) ν ∧
      (∫ y, f (x, y) ∂ν) ≤ C) :
    Integrable f (μ.prod ν) ∧ (∫ p, f p ∂μ.prod ν) ≤ C := by
  have hnorm (x : Ω) : (∫ y, ‖f (x, y)‖ ∂ν) = ∫ y, f (x, y) ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y ↦ Real.norm_of_nonneg (hn (x, y)))
  have hi : Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂ν) μ := by
    apply (integrable_const C).mono_nonneg hf.norm.integral_prod_right'.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ integral_nonneg (fun y ↦ norm_nonneg _)))
    exact Filter.Eventually.of_forall (fun x ↦ by rw [hnorm]; exact (hsection x).2)
  have hp : Integrable f (μ.prod ν) := (integrable_prod_iff hf.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall (fun x ↦ (hsection x).1), hi⟩
  refine ⟨hp, ?_⟩
  rw [integral_prod f hp]
  calc
    _ ≤ ∫ _ : Ω, C ∂μ := integral_mono hp.integral_prod_left (integrable_const C)
      (fun x ↦ (hsection x).2)
    _ = C := by simp

/-- Probability-weighted section bounds retain the full event probability after endpoint integration. -/
theorem product_nonnegative_event_moment {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω × Ξ → ℝ) (hf : StronglyMeasurable f) (hn : ∀ p, 0 ≤ f p)
    (E : Set (Ω × Ξ)) (hE : MeasurableSet E) (C : ℝ) (hC : 0 ≤ C)
    (hsection : ∀ x, Integrable (fun y ↦ f (x, y)) ν ∧
      (∫ y, f (x, y) ∂ν) ≤ C * ν.real (Prod.mk x ⁻¹' E)) :
    Integrable f (μ.prod ν) ∧ (∫ p, f p ∂μ.prod ν) ≤ C * (μ.prod ν).real E := by
  have hp := product_nonnegative_moment μ ν f hf hn C (fun x ↦
    ⟨(hsection x).1, (hsection x).2.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (measureReal_le_one (μ := ν) (s := Prod.mk x ⁻¹' E)) hC)⟩)
  let g : Ω × Ξ → ℝ := E.indicator (fun _ ↦ C)
  have hg : Integrable g (μ.prod ν) := (integrable_const C).indicator hE
  have hgi (x : Ω) : (∫ y, g (x, y) ∂ν) = C * ν.real (Prod.mk x ⁻¹' E) := by
    have he : (fun y ↦ g (x, y)) = (Prod.mk x ⁻¹' E).indicator (fun _ ↦ C) := by
      funext y
      by_cases hy : (x, y) ∈ E <;> simp [g, hy]
    rw [he, integral_indicator (hE.preimage measurable_prodMk_left)]
    simp [mul_comm]
  refine ⟨hp.1, ?_⟩
  calc
    _ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := integral_prod f hp.1
    _ ≤ ∫ x, ∫ y, g (x, y) ∂ν ∂μ := integral_mono hp.1.integral_prod_left
      hg.integral_prod_left (fun x ↦ by rw [hgi]; exact (hsection x).2)
    _ = ∫ p, g p ∂μ.prod ν := (integral_prod g hg).symm
    _ = _ := by rw [show g = E.indicator (fun _ ↦ C) from rfl, integral_indicator hE];
                simp [mul_comm]

end SRWTightness
