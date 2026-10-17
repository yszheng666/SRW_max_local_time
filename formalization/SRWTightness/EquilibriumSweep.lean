import SRWTightness.GreenRepresentation
import SRWTightness.EquilibriumProbability

namespace SRWTightness

/-- Equilibrium averaging is unchanged by enlarging a set outside which the test function is harmonic. -/
theorem equilibrium_sweep (D K L : Finset Site) (hKL : K ⊆ L) (hLD : L ⊆ D)
    (f : Site → ℝ) (hf : ∀ x, x ∉ D → f x = 0)
    (hh : ∀ x ∈ D, x ∉ K → f x = (1 / 4 : ℝ) * ∑ d : Direction, f (x + step d)) :
    ∑ x ∈ L, equilibriumMeasure D L x * f x = ∑ x ∈ K, equilibriumMeasure D K x * f x := by
  let c : Site → ℝ := fun x ↦ f x - (1 / 4 : ℝ) * ∑ d : Direction, f (x + step d)
  have hc (x : Site) (hx : x ∈ D) (hxK : x ∉ K) : c x = 0 := by
    dsimp [c]
    rw [hh x hx hxK, sub_self]
  have hre (x : Site) : f x = ∑ y ∈ K, killedGreen D x y * c y := by
    rw [green_representation D f hf x]
    apply (Finset.sum_subset (hKL.trans hLD) ?_).symm
    intro y hy hyK
    rw [show f y - (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d) = 0 from hc y hy hyK, mul_zero]
  have hs (A : Finset Site) (hKA : K ⊆ A) (hAD : A ⊆ D) :
      ∑ x ∈ A, equilibriumMeasure D A x * f x = ∑ y ∈ K, c y := by
    simp_rw [hre, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    calc
      _ = (∑ x ∈ A, equilibriumMeasure D A x * killedGreen D x y) * c y := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = c y := by rw [equilibrium_green_on_set D A hAD y (hKA hy), one_mul]
  rw [hs L hKL hLD, hs K (Finset.Subset.refl K) (hKL.trans hLD)]

end SRWTightness
