import SRWTightness.ExitLocation
import SRWTightness.OccupationFirstStep
import SRWTightness.TailRecurrence

open MeasureTheory

namespace SRWTightness

 theorem domainExitLocation_zero_of_not_mem (D : Finset Site) (x : Site) (hx : x ∉ D)
    (ω : Sample) : domainExitLocation D x ω = x := by
  unfold domainExitLocation domainSteps
  rw [domainExit_eq_zero_of_not_mem D x hx ω]
  simp

 theorem domainExitLocation_first_step (D : Finset Site) (x : Site) (hx : x ∈ D)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    domainExitLocation D x ω = domainExitLocation D (x + step (ω 0)) (shift 1 ω) := by
  unfold domainExitLocation
  rw [domainSteps_first_step D x hx ω hfin, Nat.add_comm 1, position_after_first, add_assoc]

noncomputable def exitPayoff (D : Finset Site) (f : Site → ℝ) (x : Site) : ℝ :=
  ∫ ω, f (domainExitLocation D x ω) ∂pathLaw

 theorem exitPayoff_eq_of_not_mem (D : Finset Site) (f : Site → ℝ) (x : Site) (hx : x ∉ D) :
    exitPayoff D f x = f x := by
  simp [exitPayoff, domainExitLocation_zero_of_not_mem D x hx]

 theorem exitPayoff_first_step (D : Finset Site) (f : Site → ℝ) (x : Site) (hx : x ∈ D) :
    exitPayoff D f x = (1 / 4 : ℝ) * ∑ d : Direction, exitPayoff D f (x + step d) := by
  have he : (fun ω ↦ f (domainExitLocation D x ω)) =ᵐ[pathLaw]
      (fun ω ↦ f (domainExitLocation D (x + step (ω 0)) (shift 1 ω))) := by
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    rw [domainExitLocation_first_step D x hx ω hω]
  unfold exitPayoff
  rw [integral_congr_ae he, integral_first_step_future
    (fun d ω ↦ f (domainExitLocation D (x + step d) ω))
    (fun d ↦ (measurable_of_countable f).comp (measurable_domainExitLocation D _))
    (fun d ↦ integrable_domainExit_payoff D _ f)]
  exact integral_direction_average _

end SRWTightness
