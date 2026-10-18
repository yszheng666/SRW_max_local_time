import SRWTightness.GreenDomainDecomposition
import SRWTightness.GreenSymmetry

namespace SRWTightness

/-- Extending a killed Green kernel by zero preserves symmetry at every pair of lattice sites. -/
theorem killedGreen_symm_everywhere (D : Finset Site) (x y : Site) :
    killedGreen D x y = killedGreen D y x := by
  by_cases hx : x ∈ D
  · by_cases hy : y ∈ D
    · exact killedGreen_symm D x y hx hy
    · rw [killedGreen_zero_of_target_not_mem D x y hy, killedGreen_zero_of_not_mem D y x hy]
  · rw [killedGreen_zero_of_not_mem D x y hx, killedGreen_zero_of_target_not_mem D y x hx]

/-- A nested-domain Green difference is harmonic in its second coordinate as well. -/
theorem green_difference_harmonic_right (D E : Finset Site) (hED : E ⊆ D)
    (x y : Site) (hy : y ∈ E) :
    killedGreen D x y - killedGreen E x y = (1 / 4 : ℝ) *
      ∑ d : Direction, (killedGreen D x (y + step d) - killedGreen E x (y + step d)) := by
  calc
    _ = killedGreen D y x - killedGreen E y x := by
      rw [killedGreen_symm_everywhere D x y, killedGreen_symm_everywhere E x y]
    _ = _ := green_difference_harmonic D E hED y x hy
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [killedGreen_symm_everywhere D (y + step d) x,
        killedGreen_symm_everywhere E (y + step d) x]

end SRWTightness
