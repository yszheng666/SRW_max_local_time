import SRWTightness.GaussianProcessLawUniqueness
import SRWTightness.ActualIntervalBridge

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The centered bridge covariance is invariant under reversal of both times. -/
theorem interval_bridge_covariance_reversal (T s t : ℝ) (hT : 0 < T) :
    min (T - s) (T - t) - (T - s) * (T - t) / T = min s t - s * t / T := by
  rcases le_total s t with h | h
  · rw [min_eq_left h, min_eq_right (by linarith)]
    field_simp
    ring
  · rw [min_eq_right h, min_eq_left (by linarith)]
    field_simp
    ring

/-- Reversing time preserves the full measurable centered bridge path law. -/
theorem actualIntervalBridge_reversed_path_law (T : ℝ) (hT : 0 < T) :
    gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) T) ↦ actualIntervalBridge T (T - t) ω) =
    gaussianCoefficientLaw.map
      (fun ω (t : Set.Icc (0 : ℝ) T) ↦ actualIntervalBridge T t ω) := by
  let r : Set.Icc (0 : ℝ) T → Set.Icc (0 : ℝ) T := fun t ↦
    ⟨T - t, by constructor <;> linarith [t.property.1, t.property.2]⟩
  apply gaussian_process_law_eq_of_mean_covariance gaussianCoefficientLaw _ _
    ((actualIntervalBridge_gaussian T hT).comp_right r)
    (actualIntervalBridge_gaussian T hT)
  · exact measurable_pi_lambda _ (fun t ↦ actualIntervalBridge_measurable T (T - t))
  · exact measurable_pi_lambda _ (fun t ↦ actualIntervalBridge_measurable T t)
  · intro t
    dsimp only [Function.comp_def, r]
    rw [actualIntervalBridge_mean T (T - t) hT (r t).property.1 (r t).property.2,
      actualIntervalBridge_mean T t hT t.property.1 t.property.2]
  · intro s t
    dsimp only [Function.comp_def, r]
    rw [actualIntervalBridge_covariance T (T - s) (T - t) hT
      (r s).property.1 (r s).property.2 (r t).property.1 (r t).property.2,
      actualIntervalBridge_covariance T s t hT s.property.1 s.property.2
        t.property.1 t.property.2]
    exact interval_bridge_covariance_reversal T s t hT

end SRWTightness
