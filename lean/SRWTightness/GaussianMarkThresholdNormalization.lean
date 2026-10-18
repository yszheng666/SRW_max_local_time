import SRWTightness.GaussianOccupationComparison

namespace SRWTightness

/-- Exact normalization of the positive Gaussian branch for fixed-count marks. -/
theorem gaussian_mark_threshold_normalization (k a : ℕ) (α g : ℝ) (hα : 0 ≤ α) :
    (Real.sqrt (2 * (a : ℝ)) - Real.sqrt (2 * ((k : ℝ) * α))) / Real.sqrt g =
      Real.sqrt (2 * (a : ℝ) / g) - Real.sqrt (α / g) * Real.sqrt (2 * (k : ℝ)) := by
  rw [Real.sqrt_div (show 0 ≤ 2 * (a : ℝ) by positivity) g, Real.sqrt_div hα g]
  have he : 2 * ((k : ℝ) * α) = (2 * (k : ℝ)) * α := by ring
  rw [he, Real.sqrt_mul (show 0 ≤ 2 * (k : ℝ) by positivity) α]
  ring

/-- The raw upper-branch event equals the normalized manuscript threshold event. -/
theorem gaussian_mark_threshold_event (A : Finset Site) (k a : ℕ) (α g : ℝ)
    (hα : 0 ≤ α) (hg : 0 < g) :
    {φ : EuclideanSpace ℝ A | ∃ z : A,
      Real.sqrt (2 * (a : ℝ)) - Real.sqrt (2 * ((k : ℝ) * α)) ≤ φ z} =
    {φ | ∃ z : A, Real.sqrt (2 * (a : ℝ) / g) -
      Real.sqrt (α / g) * Real.sqrt (2 * (k : ℝ)) ≤ φ z / Real.sqrt g} := by
  ext φ
  simp only [Set.mem_setOf_eq]
  apply exists_congr
  intro z
  rw [← gaussian_mark_threshold_normalization k a α g hα]
  exact (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hg)).symm

end SRWTightness
