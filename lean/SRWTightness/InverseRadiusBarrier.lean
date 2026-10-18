import SRWTightness.InverseRadiusBarrierAlgebra
import SRWTightness.Geometry
import Mathlib.Algebra.BigOperators.Fin

namespace SRWTightness

theorem inverse_normSq_submean (z : Site) (hz : 4 ≤ normSq z) :
    1 / normSq z ≤ (1 / 4 : ℝ) * ∑ d : Direction, 1 / normSq (z + step d) := by
  have h := inverse_radius_submean (z.1 : ℝ) (z.2 : ℝ) (normSq z) rfl hz
  have h0 : normSq (z + step 0) = normSq z + 1 + 2 * (z.1 : ℝ) := by
    rw [show step (0 : Direction) = (1, 0) from rfl]
    norm_num [normSq]
    ring
  have h1 : normSq (z + step 1) = normSq z + 1 - 2 * (z.1 : ℝ) := by
    rw [show step (1 : Direction) = (-1, 0) from rfl]
    norm_num [normSq]
    ring
  have h2 : normSq (z + step 2) = normSq z + 1 + 2 * (z.2 : ℝ) := by
    rw [show step (2 : Direction) = (0, 1) from rfl]
    norm_num [normSq]
    ring
  have h3 : normSq (z + step 3) = normSq z + 1 - 2 * (z.2 : ℝ) := by
    rw [show step (3 : Direction) = (0, -1) from rfl]
    norm_num [normSq]
    ring
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  convert h using 1 <;> ring

/-- An explicit superharmonic radial barrier for the actual four-neighbor SRW.
Annulus stopping and the boundary-weight estimate are not asserted here. -/
theorem inverse_normSq_barrier_supermean (z : Site) (hz : 4 ≤ normSq z)
    (A : ℝ) (hA : 0 ≤ A) :
    (1 / 4 : ℝ) * ∑ d : Direction, (1 - A / normSq (z + step d)) ≤ 1 - A / normSq z := by
  have hh := mul_le_mul_of_nonneg_left (inverse_normSq_submean z hz) hA
  have he : (1 / 4 : ℝ) * ∑ d : Direction, (1 - A / normSq (z + step d)) =
      1 - A * ((1 / 4 : ℝ) * ∑ d : Direction, 1 / normSq (z + step d)) := by
    rw [Fin.sum_univ_four, Fin.sum_univ_four]
    ring
  rw [he]
  have ha : A * (1 / normSq z) = A / normSq z := by ring
  rw [ha] at hh
  linarith

end SRWTightness
