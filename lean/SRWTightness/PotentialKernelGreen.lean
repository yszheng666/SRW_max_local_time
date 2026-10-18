import SRWTightness.PotentialKernelPoisson
import SRWTightness.PoissonBoundary
import SRWTightness.GreenDomainDecomposition
import Mathlib.Tactic.Abel

namespace SRWTightness

/-- The actual Fourier potential kernel, translated to any lattice target, solves the Poisson equation. -/
theorem potentialKernel_poisson_translate (w y : Site) :
    (1 / 4 : ℝ) * ∑ d : Direction, potentialKernel (w + step d - y) - potentialKernel (w - y) =
      if w = y then 1 else 0 := by
  have he := potentialKernel_poisson (w - y)
  have hs (d : Direction) : w + step d - y = w - y + step d := by abel
  simp only [hs, sub_eq_zero] at he ⊢
  exact he

/-- Manuscript (2.6) for the explicitly constructed SRW potential kernel. -/
theorem potentialKernel_green_representation (D : Finset Site) (x y : Site) :
    killedGreen D x y = exitPayoff D (fun w ↦ potentialKernel (w - y)) x - potentialKernel (x - y) := by
  rw [poisson_boundary_formula]
  simp_rw [potentialKernel_poisson_translate]
  by_cases hy : y ∈ D
  · simp [hy]
  · simp [hy, killedGreen_zero_of_target_not_mem D x y hy]

end SRWTightness
