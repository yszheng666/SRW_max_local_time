import SRWTightness.StepExpectation

open MeasureTheory

namespace SRWTightness

/-- Integrating a single direction uses exactly its four-point marginal. -/
theorem integral_direction (n : ℕ) (f : Direction → ℝ) :
    ∫ ω, f (ω n) ∂pathLaw = ∫ d, f d ∂directionLaw := by
  rw [← direction_marginal n]
  exact (integral_map (measurable_pi_apply n).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable).symm

 theorem integral_step_fst : ∫ d, ((step d).1 : ℝ) ∂directionLaw = 0 := by
  rw [directionLaw, PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, Direction, Fin.sum_univ_succ, step]

 theorem integral_step_snd : ∫ d, ((step d).2 : ℝ) ∂directionLaw = 0 := by
  rw [directionLaw, PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, Direction, Fin.sum_univ_succ, step]

 theorem integral_increment_fst (n : ℕ) :
    ∫ ω, ((step (ω n)).1 : ℝ) ∂pathLaw = 0 := by
  exact (integral_direction n (fun d ↦ ((step d).1 : ℝ))).trans integral_step_fst

 theorem integral_increment_snd (n : ℕ) :
    ∫ ω, ((step (ω n)).2 : ℝ) ∂pathLaw = 0 := by
  exact (integral_direction n (fun d ↦ ((step d).2 : ℝ))).trans integral_step_snd

end SRWTightness
