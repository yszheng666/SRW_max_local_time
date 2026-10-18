import SRWTightness.DiskEquilibriumWeightBound
import SRWTightness.CapacityEnergyParameters

namespace SRWTightness

theorem equilibriumWeight_translate (b : Site) (D K : Finset Site) (x : Site) :
    equilibriumWeight (translateFinset b D) (translateFinset b K) (b + x) =
      equilibriumWeight D K x := by
  simp only [equilibriumWeight, equilibriumMeasure_translate, capacity_translate]

/-- The squared norm follows from the pointwise bound and unit total mass. -/
theorem equilibriumWeight_sq_sum_le_pointwise (D K : Finset Site) (hKD : K ⊆ D)
    (hne : K.Nonempty) (C : ℝ) (hC : ∀ x ∈ K, equilibriumWeight D K x ≤ C) :
    ∑ x ∈ K, equilibriumWeight D K x ^ 2 ≤ C := by
  calc
    _ ≤ ∑ x ∈ K, C * equilibriumWeight D K x := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_right (hC x hx) (equilibriumWeight_nonneg D K x)
    _ = C := by rw [← Finset.mul_sum, equilibriumWeight_sum D K hKD hne, mul_one]

theorem equilibriumWeight_translated_radius_upper (b : Site) (a R : ℝ) (ha : 4 ≤ a)
    (hRa : 2 * a ≤ R) (x : Site) :
    equilibriumWeight (translateFinset b (diskFinset R)) (translateFinset b (diskFinset a)) x ≤
      diskEquilibriumWeightConstant / a := by
  have h := equilibriumWeight_disk_radius_upper a R ha hRa (x - b)
  rw [← equilibriumWeight_translate b] at h
  simpa only [show b + (x - b) = x by abel] using h

theorem equilibriumWeight_translated_sq_sum_upper (b : Site) (a R : ℝ) (ha : 4 ≤ a)
    (hRa : 2 * a ≤ R) :
    ∑ x ∈ translateFinset b (diskFinset a),
      equilibriumWeight (translateFinset b (diskFinset R)) (translateFinset b (diskFinset a)) x ^ 2 ≤
        diskEquilibriumWeightConstant / a := by
  have hKD : translateFinset b (diskFinset a) ⊆ translateFinset b (diskFinset R) := by
    apply Finset.image_subset_image
    exact diskFinset_mono a R (by linarith) (by linarith)
  have hne : (translateFinset b (diskFinset a)).Nonempty := by
    exact Finset.Nonempty.image ⟨0, zero_mem_diskFinset a (by linarith)⟩ _
  exact equilibriumWeight_sq_sum_le_pointwise _ _ hKD hne _
    (fun x _ ↦ equilibriumWeight_translated_radius_upper b a R ha hRa x)

/-- Manuscript (2.12) in its large-radius regime with explicit scale separation. -/
theorem equilibriumWeight_source_bounds (b : Site) (m a H : ℝ) (ha : 4 ≤ a)
    (hma : 2 * a ≤ m) (hH : |H| ≤ m / 2) :
    (∀ x, equilibriumWeight (translateFinset b (diskFinset (Real.exp 1 * m + H)))
      (translateFinset b (diskFinset a)) x ≤ diskEquilibriumWeightConstant / a) ∧
    (∑ x ∈ translateFinset b (diskFinset a),
      equilibriumWeight (translateFinset b (diskFinset (Real.exp 1 * m + H)))
        (translateFinset b (diskFinset a)) x ^ 2 ≤ diskEquilibriumWeightConstant / a) := by
  have hm : 0 < m := by linarith
  have hHl := (abs_le.mp hH).1
  have hRm : m ≤ Real.exp 1 * m + H := by nlinarith [Real.exp_one_gt_two]
  exact ⟨equilibriumWeight_translated_radius_upper b a _ ha (hma.trans hRm),
    equilibriumWeight_translated_sq_sum_upper b a _ ha (hma.trans hRm)⟩

end SRWTightness
