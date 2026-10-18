import SRWTightness.Law
import SRWTightness.StepBound

open MeasureTheory

namespace SRWTightness

 theorem measurable_normSq_position (n : ℕ) :
    Measurable (fun ω ↦ normSq (position ω n)) :=
  (measurable_of_countable normSq).comp (measurable_position n)

 theorem integrable_normSq_position (n : ℕ) :
    Integrable (fun ω ↦ normSq (position ω n)) pathLaw := by
  refine ⟨(measurable_normSq_position n).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := (n : ℝ) ^ 2) ?_⟩
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg _)] using
    normSq_position_le ω n

end SRWTightness
