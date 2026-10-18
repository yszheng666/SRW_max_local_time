import SRWTightness.DyadicFlatPathEvent
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Raising the endpoint decreases the actual bridge flat-barrier probability. -/
theorem bridge_flat_probability_antitone (T q : ℝ) (hT : 0 < T) :
    Antitone (fun b ↦ gaussianCoefficientLaw.real (bridgeFlatEvent T b q)) := by
  intro a b hab
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω t ht
  have hw := hω t ht
  have hm := mul_le_mul_of_nonneg_left hab (div_nonneg ht.1 hT.le)
  dsimp only [endpointBrownianBridge] at hw ⊢
  linarith

/-- The actual bridge flat-barrier probability is a measurable function of its endpoint. -/
theorem bridge_flat_probability_measurable (T q : ℝ) (hT : 0 < T) :
    Measurable (fun b ↦ gaussianCoefficientLaw.real (bridgeFlatEvent T b q)) :=
  (bridge_flat_probability_antitone T q hT).measurable

/-- The actual bridge flat-barrier probability is integrable under every finite endpoint measure. -/
theorem bridge_flat_probability_integrable (T q : ℝ) (hT : 0 < T)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun b ↦ gaussianCoefficientLaw.real (bridgeFlatEvent T b q)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (bridge_flat_probability_measurable T q hT).aestronglyMeasurable
  filter_upwards [] with b
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

end SRWTightness
