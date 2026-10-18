import SRWTightness.MaximumPrinciple

open MeasureTheory

namespace SRWTightness

/-- Boundary comparison needs only points reachable at the actual exit, including overshoot. -/
theorem exitPayoff_mono_on_exitRange (D : Finset Site) (f g : Site → ℝ) (x : Site)
    (hfg : ∀ y ∈ domainExitRange D x, y ∉ D → f y ≤ g y) :
    exitPayoff D f x ≤ exitPayoff D g x := by
  apply integral_mono_ae (integrable_domainExit_payoff D x f) (integrable_domainExit_payoff D x g)
  filter_upwards [domainExit_ne_top_ae D x] with ω hω
  exact hfg _ (domainExitLocation_mem_range D x ω) (position_domain_exit_not_mem D x ω hω)

theorem exitPayoff_affine (D : Finset Site) (f : Site → ℝ) (x : Site) (a b : ℝ) :
    exitPayoff D (fun y ↦ a + b * f y) x = a + b * exitPayoff D f x := by
  unfold exitPayoff
  rw [integral_add (integrable_const a) ((integrable_domainExit_payoff D x f).const_mul b),
    integral_const_mul]
  simp

end SRWTightness
