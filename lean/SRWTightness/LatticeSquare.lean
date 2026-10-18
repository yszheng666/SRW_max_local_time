import SRWTightness.Geometry
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval

namespace SRWTightness

/-- The N by N lattice box including its fixed-zero boundary vertices. -/
def latticeSquare (a : Site) (N : ℕ) : Finset Site :=
  (Finset.Icc a.1 (a.1 + (N : ℤ) - 1)).product
    (Finset.Icc a.2 (a.2 + (N : ℤ) - 1))

/-- Killing on leaving this interior corresponds to zero data on the surrounding box boundary. -/
def latticeSquareInterior (a : Site) (N : ℕ) : Finset Site :=
  (Finset.Icc (a.1 + 1) (a.1 + (N : ℤ) - 2)).product
    (Finset.Icc (a.2 + 1) (a.2 + (N : ℤ) - 2))

theorem mem_latticeSquareInterior (a x : Site) (N : ℕ) :
    x ∈ latticeSquareInterior a N ↔
      (a.1 + 1 ≤ x.1 ∧ x.1 ≤ a.1 + (N : ℤ) - 2) ∧
      (a.2 + 1 ≤ x.2 ∧ x.2 ≤ a.2 + (N : ℤ) - 2) := by
  simp [latticeSquareInterior]

theorem latticeSquareInterior_subset (a : Site) (N : ℕ) :
    latticeSquareInterior a N ⊆ latticeSquare a N := by
  intro x hx
  simp only [mem_latticeSquareInterior] at hx
  simp only [latticeSquare, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  omega

theorem latticeSquareInterior_nonempty (a : Site) (N : ℕ) (hN : 3 ≤ N) :
    (latticeSquareInterior a N).Nonempty := by
  refine ⟨(a.1 + 1, a.2 + 1), ?_⟩
  rw [mem_latticeSquareInterior]
  simp only [Prod.fst, Prod.snd]
  omega

end SRWTightness
