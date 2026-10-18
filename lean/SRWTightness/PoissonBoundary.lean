import SRWTightness.ExitPayoff
import SRWTightness.GreenRepresentation

namespace SRWTightness

/-- Finite-domain Poisson representation, with the true exit distribution. -/
theorem poisson_boundary_formula (D : Finset Site) (f : Site → ℝ) (x : Site) :
    exitPayoff D f x - f x = ∑ y ∈ D, killedGreen D x y *
      ((1 / 4 : ℝ) * ∑ d : Direction, f (y + step d) - f y) := by
  let u : Site → ℝ := fun y ↦ exitPayoff D f y - f y
  have hu : ∀ y, y ∉ D → u y = 0 := by
    intro y hy
    simp [u, exitPayoff_eq_of_not_mem D f y hy]
  have he (y : Site) (hy : y ∈ D) : u y - (1 / 4 : ℝ) *
      ∑ d : Direction, u (y + step d) = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d) - f y := by
    dsimp [u]
    rw [Finset.sum_sub_distrib, mul_sub, ← exitPayoff_first_step D f y hy]
    ring
  change u x = _
  rw [green_representation D u hu x]
  apply Finset.sum_congr rfl
  intro y hy
  rw [he y hy]

/-- The stopping identity required for a potential kernel. The kernel itself and its asymptotics
are separate obligations, not assumptions of any tightness theorem. -/
theorem green_from_poisson_kernel (D : Finset Site) (a : Site → ℝ) (x y : Site)
    (hy : y ∈ D)
    (ha : ∀ w ∈ D, (1 / 4 : ℝ) * ∑ d : Direction, a (w + step d - y) - a (w - y) =
      if w = y then 1 else 0) :
    killedGreen D x y = exitPayoff D (fun w ↦ a (w - y)) x - a (x - y) := by
  rw [poisson_boundary_formula]
  have he : (∑ w ∈ D, killedGreen D x w *
      ((1 / 4 : ℝ) * ∑ d : Direction, a (w + step d - y) - a (w - y))) =
      ∑ w ∈ D, killedGreen D x w * (if w = y then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [ha w hw]
  rw [he]
  simp [hy]

end SRWTightness
