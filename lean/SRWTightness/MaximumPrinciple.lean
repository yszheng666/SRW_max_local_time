import SRWTightness.PoissonBoundary
import SRWTightness.SetHitting

open MeasureTheory

namespace SRWTightness

 theorem exitPayoff_mono_on_compl (D : Finset Site) (f g : Site → ℝ)
    (hfg : ∀ y, y ∉ D → f y ≤ g y) (x : Site) : exitPayoff D f x ≤ exitPayoff D g x := by
  apply integral_mono_ae (integrable_domainExit_payoff D x f) (integrable_domainExit_payoff D x g)
  filter_upwards [domainExit_ne_top_ae D x] with ω hω
  exact hfg _ (position_domain_exit_not_mem D x ω hω)

 theorem subharmonic_le_exitPayoff (D : Finset Site) (f : Site → ℝ)
    (hh : ∀ y ∈ D, f y ≤ (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d)) (x : Site) :
    f x ≤ exitPayoff D f x := by
  have he := poisson_boundary_formula D f x
  have hn : 0 ≤ ∑ y ∈ D, killedGreen D x y *
      ((1 / 4 : ℝ) * ∑ d : Direction, f (y + step d) - f y) :=
    Finset.sum_nonneg (fun y hy ↦ mul_nonneg (killedGreen_nonneg D x y) (sub_nonneg.mpr (hh y hy)))
  linarith

 theorem exitPayoff_le_superharmonic (D : Finset Site) (f : Site → ℝ)
    (hh : ∀ y ∈ D, (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d) ≤ f y) (x : Site) :
    exitPayoff D f x ≤ f x := by
  have he := poisson_boundary_formula D f x
  have hn : (∑ y ∈ D, killedGreen D x y *
      ((1 / 4 : ℝ) * ∑ d : Direction, f (y + step d) - f y)) ≤ 0 :=
    Finset.sum_nonpos (fun y hy ↦ mul_nonpos_of_nonneg_of_nonpos
      (killedGreen_nonneg D x y) (sub_nonpos.mpr (hh y hy)))
  linarith

/-- The finite-domain comparison principle used to propagate entrance-law errors. -/
theorem finite_domain_comparison (D : Finset Site) (f g : Site → ℝ)
    (hf : ∀ y ∈ D, f y ≤ (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d))
    (hg : ∀ y ∈ D, (1 / 4 : ℝ) * ∑ d : Direction, g (y + step d) ≤ g y)
    (hfg : ∀ y, y ∉ D → f y ≤ g y) (x : Site) : f x ≤ g x :=
  (subharmonic_le_exitPayoff D f hf x).trans
    ((exitPayoff_mono_on_compl D f g hfg x).trans (exitPayoff_le_superharmonic D g hg x))

 theorem harmonic_eq_exitPayoff (D : Finset Site) (f : Site → ℝ)
    (hh : ∀ y ∈ D, f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d)) (x : Site) :
    f x = exitPayoff D f x :=
  le_antisymm (subharmonic_le_exitPayoff D f (fun y hy ↦ (hh y hy).le) x)
    (exitPayoff_le_superharmonic D f (fun y hy ↦ (hh y hy).ge) x)

end SRWTightness
