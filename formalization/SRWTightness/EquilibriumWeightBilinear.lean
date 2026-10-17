import SRWTightness.Capacity
import SRWTightness.CapacityMonotone

namespace SRWTightness

theorem equilibriumWeight_zero_of_not_mem (D K : Finset Site) (x : Site) (hx : x ∉ K) :
    equilibriumWeight D K x = 0 := by
  simp [equilibriumWeight, equilibriumMeasure, hx]

theorem equilibriumWeight_sum_over (D A K : Finset Site) (hKA : K ⊆ A) (hKD : K ⊆ D)
    (hne : K.Nonempty) : (∑ x ∈ A, equilibriumWeight D K x) = 1 := by
  rw [← equilibriumWeight_sum D K hKD hne]
  symm
  exact Finset.sum_subset hKA (fun x _ hx ↦ equilibriumWeight_zero_of_not_mem D K x hx)

theorem equilibriumWeight_green_over (D A K : Finset Site) (hKA : K ⊆ A) (hKD : K ⊆ D)
    (z : Site) (hz : z ∈ K) :
    (∑ x ∈ A, equilibriumWeight D K x * killedGreen D x z) = 1 / capacity D K := by
  rw [← equilibriumWeight_green D K hKD z hz]
  symm
  apply Finset.sum_subset hKA
  intro x _ hx
  rw [equilibriumWeight_zero_of_not_mem D K x hx, zero_mul]

theorem equilibriumWeight_green_right_over (D A K : Finset Site) (hKA : K ⊆ A) (hAD : A ⊆ D)
    (z : Site) (hz : z ∈ K) :
    (∑ x ∈ A, killedGreen D z x * equilibriumWeight D K x) = 1 / capacity D K := by
  rw [← equilibriumWeight_green_over D A K hKA (hKA.trans hAD) z hz]
  apply Finset.sum_congr rfl
  intro x hx
  rw [killedGreen_symm D z x (hAD (hKA hz)) (hAD hx), mul_comm]

/-- Nested equilibrium averages have the exact reciprocal-capacity Green pairing. -/
theorem equilibriumWeight_bilinear_nested (D A K L : Finset Site)
    (hKL : K ⊆ L) (hLA : L ⊆ A) (hAD : A ⊆ D) (hne : K.Nonempty) :
    (∑ y ∈ A, ∑ z ∈ A, equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D L z) =
      1 / capacity D L := by
  have hKA := hKL.trans hLA
  have he (y : Site) (hy : y ∈ K) :
      (∑ z ∈ A, equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D L z) =
        equilibriumWeight D K y * (1 / capacity D L) := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [equilibriumWeight_green_right_over D A L hLA hAD y (hKL hy)]
  calc
    _ = ∑ y ∈ K, ∑ z ∈ A, equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D L z := by
      symm
      apply Finset.sum_subset hKA
      intro y _ hy
      simp only [equilibriumWeight_zero_of_not_mem D K y hy, zero_mul, Finset.sum_const_zero]
    _ = ∑ y ∈ K, equilibriumWeight D K y * (1 / capacity D L) := Finset.sum_congr rfl he
    _ = _ := by rw [← Finset.sum_mul, equilibriumWeight_sum D K (hKA.trans hAD) hne, one_mul]

theorem equilibriumWeight_bilinear_self (D A K : Finset Site) (hKA : K ⊆ A) (hAD : A ⊆ D)
    (hne : K.Nonempty) :
    (∑ y ∈ A, ∑ z ∈ A, equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D K z) =
      1 / capacity D K :=
  equilibriumWeight_bilinear_nested D A K K (Finset.Subset.refl K) hKA hAD hne

end SRWTightness
