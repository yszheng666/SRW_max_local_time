import SRWTightness.BufferedRecordGeometry
import SRWTightness.DiskCapacityLogBound

namespace SRWTightness

/-- A long buffered domain contains the short disk and its inner target. -/
theorem buffered_long_domains_nested (ρ H J : ℝ) (hH : 1 ≤ H) (hρ : 8 * H ≤ ρ)
    (hJ : 1 ≤ J) (b : Site) :
    translateFinset b (diskFinset (ρ - H)) ⊆
        translateFinset b (diskFinset (Real.exp 1 * ρ + H)) ∧
      translateFinset b (diskFinset (Real.exp 1 * ρ + H)) ⊆
        translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H)) := by
  have hρ0 : 0 ≤ ρ := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hspan := mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (show (1 : ℝ) ≤ J + 1 by linarith)) hρ0
  constructor
  · exact Finset.image_subset_image (diskFinset_mono _ _ (by linarith) (by nlinarith))
  · exact Finset.image_subset_image (diskFinset_mono _ _ (by positivity) (by linarith))

/-- Every short-exit atom is still inside the long disk and outside the next inner target. -/
theorem buffered_long_boundary_mem_annulus (ρ H J : ℝ) (hH : 1 ≤ H) (hρ : 8 * H ≤ ρ)
    (hJ : 1 ≤ J) (b x : Site)
    (hx : x ∈ domainExitBoundary (translateFinset b (diskFinset (Real.exp 1 * ρ + H)))) :
    x ∈ translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H)) \
      translateFinset b (diskFinset (ρ - H)) := by
  have hρ0 : 0 ≤ ρ := by linarith
  have hrad := translated_disk_boundary_radial b (Real.exp 1 * ρ + H) (by positivity) x hx
  have hmid := middle_boundary_layers_in_buffer (Real.sqrt (normSq (x - b))) ρ H hH (Or.inr hrad)
  have hm := buffered_middle_mem_annulus ρ H hH hρ b x hmid
  have hspan := mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (show (2 : ℝ) ≤ J + 1 by linarith)) hρ0
  have hD : translateFinset b (diskFinset (Real.exp 2 * ρ + H)) ⊆
      translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H)) :=
    Finset.image_subset_image (diskFinset_mono _ _ (by positivity) (by linarith))
  exact Finset.mem_sdiff.mpr ⟨hD (Finset.mem_sdiff.mp hm).1, (Finset.mem_sdiff.mp hm).2⟩

end SRWTightness
