import SRWTightness.SourceCandidateAnnulus
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

namespace SRWTightness

/-- A fixed proportional rectangle lies wholly in the manuscript's closed candidate annulus. -/
theorem source_annulus_rectangle_point (R : ℝ) (hR : 0 < R) (z : Site)
    (hx0 : R / 4 ≤ (z.1 : ℝ)) (hx1 : (z.1 : ℝ) ≤ 27 * R / 100)
    (hy0 : 0 ≤ (z.2 : ℝ)) (hy1 : (z.2 : ℝ) ≤ R / 100) :
    z ∈ sourceCandidateAnnulus R := by
  rw [mem_sourceCandidateAnnulus R hR]
  have hxpos : (0 : ℝ) ≤ (z.1 : ℝ) := by linarith
  have hl := mul_self_le_mul_self (by positivity : 0 ≤ R / 4) hx0
  have hu := mul_self_le_mul_self hxpos hx1
  have hv := mul_self_le_mul_self hy0 hy1
  constructor
  · apply (Real.le_sqrt (by positivity) (normSq_nonneg z)).mpr
    dsimp [normSq]
    nlinarith [sq_nonneg (z.2 : ℝ)]
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    dsimp [normSq]
    nlinarith [sq_nonneg R]

/-- Exact rounding leaves a quadratic-size integer rectangle inside the original candidate annulus.
-/
theorem source_annulus_integer_rectangle_subset (R : ℝ) (hR : 100 ≤ R) :
    (Finset.Icc ⌈R / 4⌉ (⌈R / 4⌉ + (⌊R / 100⌋₊ : ℤ))).product
      (Finset.Icc 0 (⌊R / 100⌋₊ : ℤ)) ⊆ sourceCandidateAnnulus R := by
  intro z hz
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
  obtain ⟨hx0, hx1⟩ := Finset.mem_Icc.mp hx
  obtain ⟨hy0, hy1⟩ := Finset.mem_Icc.mp hy
  have hc0 := Int.le_ceil (R / 4)
  have hc1 := Int.ceil_lt_add_one (R / 4)
  have hn := Nat.floor_le (by linarith : 0 ≤ R / 100)
  have hx0r : (⌈R / 4⌉ : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast hx0
  have hx1r : (z.1 : ℝ) ≤ (⌈R / 4⌉ : ℝ) + (⌊R / 100⌋₊ : ℝ) := by
    exact_mod_cast hx1
  have hy0r : (0 : ℝ) ≤ (z.2 : ℝ) := by exact_mod_cast hy0
  have hy1r : (z.2 : ℝ) ≤ (⌊R / 100⌋₊ : ℝ) := by exact_mod_cast hy1
  exact source_annulus_rectangle_point R (by linarith) z (by linarith) (by linarith)
    hy0r (by linarith)

/-- The rectangle's two closed integer sides each contain exactly N+1 sites. -/
theorem lattice_shifted_integer_rectangle_card (A : ℤ) (N : ℕ) :
    ((Finset.Icc A (A + (N : ℤ))).product (Finset.Icc 0 (N : ℤ))).card = (N + 1) ^ 2 := by
  have hleft : (Finset.Icc A (A + (N : ℤ))).card = N + 1 := by
    rw [Int.card_Icc]
    rw [show A + (N : ℤ) + 1 - A = ((N + 1 : ℕ) : ℤ) by omega]
    simp
  have hright : (Finset.Icc 0 (N : ℤ)).card = N + 1 := by
    rw [Int.card_Icc]
    rw [show (N : ℤ) + 1 - 0 = ((N + 1 : ℕ) : ℤ) by omega]
    simp
  have hp := Finset.card_product (Finset.Icc A (A + (N : ℤ))) (Finset.Icc 0 (N : ℤ))
  change ((Finset.Icc A (A + (N : ℤ))).product (Finset.Icc 0 (N : ℤ))).card = _ at hp
  rw [hleft, hright] at hp
  simpa only [pow_two] using hp

end SRWTightness
