import SRWTightness.DiskFiniteDomain
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.Floor.Ring

namespace SRWTightness

/-- A closed integer coordinate box has its exact quadratic number of lattice sites. -/
theorem lattice_integer_box_card (B : ℤ) (hB : 0 ≤ B) :
    (((Finset.Icc (-B) B).product (Finset.Icc (-B) B)).card : ℝ) =
      (2 * (B : ℝ) + 1) ^ 2 := by
  have hc := Int.card_Icc_of_le (a := -B) (b := B) (by omega : -B ≤ B + 1)
  have hreal : ((Finset.Icc (-B) B).card : ℝ) = 2 * (B : ℝ) + 1 := by
    have hh : ((Finset.Icc (-B) B).card : ℝ) = (B : ℝ) + 1 - (-(B : ℝ)) := by
      exact_mod_cast hc
    linarith
  have hp : ((Finset.Icc (-B) B).product (Finset.Icc (-B) B)).card =
      (Finset.Icc (-B) B).card * (Finset.Icc (-B) B).card := Finset.card_product _ _
  calc
    _ = ((Finset.Icc (-B) B).card : ℝ) * (Finset.Icc (-B) B).card := by exact_mod_cast hp
    _ = _ := by rw [hreal]; ring

/-- Coordinate bounds inject every disk into its enclosing closed integer box. -/
theorem diskFinset_subset_integer_box (r : ℝ) (hr : 0 ≤ r) (B : ℤ)
    (hB : r ≤ (B : ℝ)) :
    diskFinset r ⊆ (Finset.Icc (-B) B).product (Finset.Icc (-B) B) := by
  intro z hz
  have hsq : normSq z ≤ r ^ 2 := (mem_diskFinset r z |>.mp hz).le
  have hx : |(z.1 : ℝ)| ≤ (B : ℝ) := (abs_fst_le_normSq_bound z hr hsq).trans hB
  have hy : |(z.2 : ℝ)| ≤ (B : ℝ) := (abs_snd_le_normSq_bound z hr hsq).trans hB
  have hxi : |z.1| ≤ B := by exact_mod_cast hx
  have hyi : |z.2| ≤ B := by exact_mod_cast hy
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hxi),
    Finset.mem_Icc.mpr (abs_le.mp hyi)⟩

end SRWTightness
