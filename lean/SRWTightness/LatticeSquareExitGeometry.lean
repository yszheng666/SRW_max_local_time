import SRWTightness.LatticeSquare
import SRWTightness.RecordExitSlice
import Mathlib.Tactic.FinCases

namespace SRWTightness

/-- Every one-step exit from a square interior stays on its surrounding lattice square. -/
theorem latticeSquareInterior_exit_mem_square (a z : Site) (N : ℕ)
    (hz : z ∈ domainExitBoundary (latticeSquareInterior a N)) : z ∈ latticeSquare a N := by
  obtain ⟨hz, w, hw, d, rfl⟩ := hz
  rw [mem_latticeSquareInterior] at hw
  simp only [latticeSquare, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  have hs : (-1 : ℤ) ≤ (step d).1 ∧ (step d).1 ≤ 1 ∧
      (-1 : ℤ) ≤ (step d).2 ∧ (step d).2 ≤ 1 := by fin_cases d <;> decide
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- A one-step exit lies on at least one of the four fixed-zero sides. -/
theorem latticeSquareInterior_exit_side (a z : Site) (N : ℕ)
    (hz : z ∈ domainExitBoundary (latticeSquareInterior a N)) :
    z.1 = a.1 ∨ z.1 = a.1 + (N : ℤ) - 1 ∨
      z.2 = a.2 ∨ z.2 = a.2 + (N : ℤ) - 1 := by
  have hb := latticeSquareInterior_exit_mem_square a z N hz
  have hout := hz.1
  rw [mem_latticeSquareInterior] at hout
  simp only [latticeSquare, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hb
  omega

end SRWTightness
