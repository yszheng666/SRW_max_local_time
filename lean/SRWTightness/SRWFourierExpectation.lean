import SRWTightness.PotentialFourierStep
import SRWTightness.FirstStepLaw
import SRWTightness.TailRecurrence
import Mathlib.Tactic.Abel

open MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def fourierCharacteristic (θ : ℝ × ℝ) : ℝ :=
  (Real.cos θ.1 + Real.cos θ.2) / 2

theorem measurable_cos_position (n : ℕ) (z : Site) (θ : ℝ × ℝ) :
    Measurable (fun ω ↦ Real.cos (fourierPhase (z + position ω n) θ)) :=
  (measurable_of_countable (fun w : Site ↦ Real.cos (fourierPhase (z + w) θ))).comp
    (measurable_position n)

theorem integrable_cos_position (n : ℕ) (z : Site) (θ : ℝ × ℝ) :
    Integrable (fun ω ↦ Real.cos (fourierPhase (z + position ω n) θ)) pathLaw := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_cos_position n z θ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)

/-- Exact Fourier eigenfunction identity for the original independent-increment SRW law. -/
theorem integral_cos_position (n : ℕ) (z : Site) (θ : ℝ × ℝ) :
    (∫ ω, Real.cos (fourierPhase (z + position ω n) θ) ∂pathLaw) =
      fourierCharacteristic θ ^ n * Real.cos (fourierPhase z θ) := by
  induction n generalizing z with
  | zero =>
    change (∫ _ : Sample, Real.cos (fourierPhase (z + (0 : Site)) θ) ∂pathLaw) = _
    simp
  | succ n ih =>
    have hp (ω : Sample) : position ω (n + 1) = step (ω 0) + position (shift 1 ω) n := by
      have he := position_add ω 1 n
      change position ω (1 + n) = (0 : Site) + step (ω 0) + position (shift 1 ω) n at he
      simpa only [Nat.add_comm 1 n, zero_add] using he
    have he : (fun ω ↦ Real.cos (fourierPhase (z + position ω (n + 1)) θ)) =
        fun ω ↦ Real.cos (fourierPhase (z + step (ω 0) + position (shift 1 ω) n) θ) := by
      funext ω
      rw [hp, add_assoc]
    rw [he, integral_first_step_future
      (fun d ω ↦ Real.cos (fourierPhase (z + step d + position ω n) θ))
      (fun d ↦ measurable_cos_position n (z + step d) θ)
      (fun d ↦ integrable_cos_position n (z + step d) θ)]
    simp_rw [ih]
    rw [integral_direction_average, ← Finset.mul_sum, sum_cos_fourierPhase_step, pow_succ]
    unfold fourierCharacteristic
    ring

end SRWTightness
