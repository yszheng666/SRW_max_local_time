import SRWTightness.QuadraticMartingale
import SRWTightness.BoundedExit
import Mathlib.Probability.Martingale.OptionalStopping

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace SRWTightness

 theorem integrable_boundedTime (R : ℝ) (N : ℕ) :
    Integrable (fun ω ↦ (boundedTime R N ω : ℝ)) pathLaw :=
  integrable_stoppedValue ℕ (boundedExit_isStoppingTime R N)
    (fun n ↦ integrable_const (n : ℝ)) (fun _ ↦ min_le_right _ _)

 theorem integrable_normSq_boundedTime (R : ℝ) (N : ℕ) :
    Integrable (fun ω ↦ normSq (position ω (boundedTime R N ω))) pathLaw :=
  integrable_stoppedValue ℕ (boundedExit_isStoppingTime R N)
    integrable_normSq_position (fun _ ↦ min_le_right _ _)

/-- Bounded optional stopping applied to the already-proved SRW martingale. -/
theorem integral_stopped_quadratic_eq_zero (R : ℝ) (N : ℕ) :
    ∫ ω, quadraticProcess (boundedTime R N ω) ω ∂pathLaw = 0 := by
  have hτ := boundedExit_isStoppingTime R N
  have hle : (fun _ : Sample ↦ ((0 : ℕ) : WithTop ℕ)) ≤ boundedExit R N :=
    fun _ ↦ bot_le
  have hb : ∀ ω, boundedExit R N ω ≤ (N : WithTop ℕ) := fun _ ↦ min_le_right _ _
  have hl := martingale_quadraticProcess.submartingale.expected_stoppedValue_mono
    (isStoppingTime_const history 0) hτ hle hb
  have hu := martingale_quadraticProcess.neg.submartingale.expected_stoppedValue_mono
    (isStoppingTime_const history 0) hτ hle hb
  have hzero : quadraticProcess 0 = 0 := by
    funext ω
    simp [quadraticProcess, position, normSq]
  have hlo : 0 ≤ ∫ ω, quadraticProcess (boundedTime R N ω) ω ∂pathLaw := by
    simpa [stoppedValue, boundedTime, WithTop.untopA, quadraticProcess, position, normSq] using hl
  have hup : ∫ ω, quadraticProcess (boundedTime R N ω) ω ∂pathLaw ≤ 0 := by
    change (∫ ω, -(quadraticProcess 0 ω) ∂pathLaw) ≤
      ∫ ω, -(quadraticProcess (boundedTime R N ω) ω) ∂pathLaw at hu
    simp only [integral_neg, hzero, Pi.zero_apply, integral_zero, neg_zero] at hu
    exact neg_nonneg.mp hu
  exact le_antisymm hup hlo

/-- Source equation (2.3), the exact stopped second-moment identity. -/
theorem integral_normSq_boundedTime_eq (R : ℝ) (N : ℕ) :
    ∫ ω, normSq (position ω (boundedTime R N ω)) ∂pathLaw =
      ∫ ω, (boundedTime R N ω : ℝ) ∂pathLaw := by
  have h := integral_stopped_quadratic_eq_zero R N
  simp only [quadraticProcess] at h
  rw [integral_sub (integrable_normSq_boundedTime R N) (integrable_boundedTime R N)] at h
  exact sub_eq_zero.mp h

 theorem integral_boundedTime_le {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ∫ ω, (boundedTime R N ω : ℝ) ∂pathLaw ≤ (R + 1) ^ 2 := by
  rw [← integral_normSq_boundedTime_eq]
  calc
    _ ≤ ∫ _ : Sample, (R + 1) ^ 2 ∂pathLaw :=
      integral_mono (integrable_normSq_boundedTime R N) (integrable_const _)
        (fun ω ↦ normSq_at_boundedTime_le hR N ω)
    _ = (R + 1) ^ 2 := by simp

end SRWTightness
