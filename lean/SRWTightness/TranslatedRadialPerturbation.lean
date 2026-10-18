import SRWTightness.GeometryTriangle
import SRWTightness.RecordRadialSupport
import SRWTightness.LatticeNorm

namespace SRWTightness

/-- Euclidean radii satisfy the triangle inequality in the actual lattice model. -/
theorem lattice_radius_add_le (x y : Site) :
    Real.sqrt (normSq (x + y)) ≤ Real.sqrt (normSq x) + Real.sqrt (normSq y) := by
  apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
  exact normSq_add_bound x y (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (le_of_eq (normSq_eq_sq_sqrt x)) (le_of_eq (normSq_eq_sq_sqrt y))

/-- Moving the observation point changes a radial distance by at most the displacement. -/
theorem lattice_radius_sub_perturbation (z y b : Site) :
    |Real.sqrt (normSq (z - y)) - Real.sqrt (normSq (z - b))| ≤
      Real.sqrt (normSq (y - b)) := by
  have hu := lattice_radius_add_le (z - b) (b - y)
  have hl := lattice_radius_add_le (z - y) (y - b)
  rw [show z - b + (b - y) = z - y by abel,
    show b - y = -(y - b) by abel, normSq_neg] at hu
  rw [show z - y + (y - b) = z - b by abel] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Actual translated disk exits have explicit distance bounds to any nearby observation point. -/
theorem translated_disk_boundary_distance (b y : Site) (R a : ℝ) (hR : 0 ≤ R)
    (hy : Real.sqrt (normSq (y - b)) ≤ a) (z : Site)
    (hz : z ∈ domainExitBoundary (translateFinset b (diskFinset R))) :
    R - (a + 1) ≤ Real.sqrt (normSq (z - y)) ∧
      Real.sqrt (normSq (z - y)) ≤ R + (a + 1) := by
  have hr := translated_disk_boundary_radial b R hR z hz
  have hp := abs_le.mp (lattice_radius_sub_perturbation z y b)
  constructor <;> linarith

end SRWTightness
