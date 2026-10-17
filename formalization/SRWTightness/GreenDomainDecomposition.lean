import SRWTightness.PoissonBoundary
import SRWTightness.OccupationMoments

open MeasureTheory

namespace SRWTightness

 theorem killedGreen_zero_of_target_not_mem (D : Finset Site) (x y : Site) (hy : y ∉ D) :
    killedGreen D x y = 0 := by
  simp [killedGreen, domainLocalTime_eq_zero_of_target_not_mem D x y hy]

/-- Exact finite-domain first-exit decomposition of the original Green kernel. -/
theorem green_domain_decomposition (D E : Finset Site) (hED : E ⊆ D) (x y : Site) :
    killedGreen D x y = killedGreen E x y + exitPayoff E (fun z ↦ killedGreen D z y) x := by
  have hp := poisson_boundary_formula E (fun z ↦ killedGreen D z y) x
  have he (w : Site) (hw : w ∈ E) :
      (1 / 4 : ℝ) * ∑ d : Direction, killedGreen D (w + step d) y - killedGreen D w y =
        -(if w = y then 1 else 0) := by
    have hh := killedGreen_first_step_sum D w y (hED hw)
    linarith
  have hs : (∑ w ∈ E, killedGreen E x w *
      ((1 / 4 : ℝ) * ∑ d : Direction, killedGreen D (w + step d) y - killedGreen D w y)) =
      -killedGreen E x y := by
    calc
      _ = ∑ w ∈ E, killedGreen E x w * (-(if w = y then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [he w hw]
      _ = _ := by
        by_cases hy : y ∈ E
        · simp [hy]
        · simp [hy, killedGreen_zero_of_target_not_mem E x y hy]
  rw [hs] at hp
  linarith

 theorem killedGreen_mono_domain (D E : Finset Site) (hED : E ⊆ D) (x y : Site) :
    killedGreen E x y ≤ killedGreen D x y := by
  rw [green_domain_decomposition D E hED x y]
  have hn : 0 ≤ exitPayoff E (fun z ↦ killedGreen D z y) x :=
    integral_nonneg (fun ω ↦ killedGreen_nonneg D _ y)
  linarith

 theorem green_difference_harmonic (D E : Finset Site) (hED : E ⊆ D)
    (x y : Site) (hx : x ∈ E) :
    killedGreen D x y - killedGreen E x y = (1 / 4 : ℝ) *
      ∑ d : Direction, (killedGreen D (x + step d) y - killedGreen E (x + step d) y) := by
  rw [Finset.sum_sub_distrib, mul_sub]
  have hd := killedGreen_first_step_sum D x y (hED hx)
  have he := killedGreen_first_step_sum E x y hx
  linarith

end SRWTightness
