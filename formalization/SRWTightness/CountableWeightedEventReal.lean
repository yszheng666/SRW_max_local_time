import SRWTightness.CountableWeightedEvent
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
namespace SRWTightness

/-- Bounded nonnegative record weights give a real expectation under the original finite measure. -/
theorem countable_weighted_event_real {Ω R : Type*} [MeasurableSpace Ω]
    [MeasurableSpace R] [MeasurableSingletonClass R] [Countable R]
    (μ κ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure κ]
    (f : Ω → R) (hf : Measurable f) (w : R → ℝ) (hw : ∀ r, w r ∈ Set.Icc (0 : ℝ) 1)
    (s : Set R) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ r ∈ s, κ.real (f ⁻¹' {r}) ≤ C * (w r * μ.real (f ⁻¹' {r}))) :
    κ.real (f ⁻¹' s) ≤ C * ∫ ω, s.indicator w (f ω) ∂μ := by
  classical
  have hnon (ω : Ω) : 0 ≤ s.indicator w (f ω) := by
    by_cases hr : f ω ∈ s <;> simp [hr, (hw (f ω)).1]
  have hbound (ω : Ω) : s.indicator w (f ω) ≤ 1 := by
    by_cases hr : f ω ∈ s <;> simp [hr, (hw (f ω)).2]
  have hi : Integrable (fun ω ↦ s.indicator w (f ω)) μ := by
    apply Integrable.of_bound ((measurable_of_countable (s.indicator w)).comp hf).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω ↦ by
      change ‖s.indicator w (f ω)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (hnon ω)]
      exact hbound ω
  have hb := countable_weighted_event_bound μ κ f hf (fun r ↦ ENNReal.ofReal (w r))
    s (ENNReal.ofReal C) (fun r hr ↦ ?_)
  · have hfun : (fun ω ↦ s.indicator (fun r ↦ ENNReal.ofReal (w r)) (f ω)) =
        (fun ω ↦ ENNReal.ofReal (s.indicator w (f ω))) := by
      funext ω
      by_cases hr : f ω ∈ s <;> simp [hr]
    rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnon)] at hb
    have hh := ENNReal.toReal_mono (by finiteness) hb
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
      ENNReal.toReal_ofReal (integral_nonneg hnon)] using hh
  · simpa only [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul (hw r).1,
      ofReal_measureReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal (h r hr)

end SRWTightness
