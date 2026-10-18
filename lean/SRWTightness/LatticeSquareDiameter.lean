import SRWTightness.LatticeSquare
import Mathlib.Tactic.Linarith

namespace SRWTightness

/-- Interior points have squared distance at most twice the square of the side length. -/
theorem latticeSquareInterior_distance_bound (a x y : Site) (N : ℕ)
    (hx : x ∈ latticeSquareInterior a N) (hy : y ∈ latticeSquareInterior a N) :
    normSq (x - y) ≤ 2 * (N : ℝ) ^ 2 := by
  rw [mem_latticeSquareInterior] at hx hy
  have hcoord (p q l : ℤ) (hp : l + 1 ≤ p ∧ p ≤ l + (N : ℤ) - 2)
      (hq : l + 1 ≤ q ∧ q ≤ l + (N : ℤ) - 2) :
      ((p : ℝ) - (q : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by
    have hb : -(N : ℤ) ≤ p - q ∧ p - q ≤ (N : ℤ) := by omega
    have hr : -(N : ℝ) ≤ (p : ℝ) - (q : ℝ) ∧
        (p : ℝ) - (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hb
    have hm := mul_nonneg
      (show 0 ≤ (N : ℝ) + ((p : ℝ) - (q : ℝ)) by linarith)
      (show 0 ≤ (N : ℝ) - ((p : ℝ) - (q : ℝ)) by linarith)
    nlinarith only [hm]
  have h1 := hcoord x.1 y.1 a.1 hx.1 hy.1
  have h2 := hcoord x.2 y.2 a.2 hx.2 hy.2
  change ((x.1 - y.1 : ℤ) : ℝ) ^ 2 + ((x.2 - y.2 : ℤ) : ℝ) ^ 2 ≤ 2 * (N : ℝ) ^ 2
  simp only [Int.cast_sub]
  nlinarith only [h1, h2]

/-- The planar supremum interface can use the universal geometric constant two. -/
theorem latticeSquareInterior_planar_bound (a x y : Site) (N : ℕ)
    (hx : x ∈ latticeSquareInterior a N) (hy : y ∈ latticeSquareInterior a N) :
    normSq (x - y) ≤ (2 * (N : ℝ)) ^ 2 := by
  have hd := latticeSquareInterior_distance_bound a x y N hx hy
  nlinarith [sq_nonneg (N : ℝ)]

end SRWTightness
