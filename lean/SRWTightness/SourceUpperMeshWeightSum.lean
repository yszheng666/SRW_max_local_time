import SRWTightness.LatticeMeshLogWeight
import SRWTightness.SourceUpperMeshDensity
import SRWTightness.SourceUpperMeshFirstHit

open Filter

namespace SRWTightness

/-- The actual source mesh weight has the manuscript quadratic spatial bound. -/
theorem source_upper_mesh_weight_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t →
      (∑ z ∈ sourceUpperMesh t j, sourceUpperMeshWeight t j z) ≤
        C * ((j : ℝ) + 1) ^ 2 * Real.exp (2 * (j : ℝ)) := by
  obtain ⟨D, hD, hdensity⟩ := source_upper_mesh_density
  refine ⟨34 * D ^ 2, by positivity, ?_⟩
  filter_upwards [source_upper_mesh_scale_conditions, hdensity] with t ht hd
  intro j hj
  let a := sourceUpperMeshSpacing t j
  let b := sourceUpperTraversalRadius t (j + 1) + sourceUpperMeshBuffer t j
  have ha : 0 < a := (ht.2 j hj).2.1
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have haR : (a : ℝ) ≤ Real.exp t := by
    have hh := (ht.2 j hj).2.2
    change (a : ℝ) ≤ Real.exp t / 4 at hh
    linarith [Real.exp_pos t]
  have hab : (a : ℝ) ≤ b := by
    have hh := source_upper_mesh_spacing_le_fine t j
    have hbuf : 0 ≤ sourceUpperMeshBuffer t j := by unfold sourceUpperMeshBuffer; positivity
    dsimp [a, b]
    linarith
  have hZ : ∀ z ∈ sourceUpperMesh t j,
      z ∈ diskFinset (Real.exp t) ∧ (a : ℤ) ∣ z.1 ∧ (a : ℤ) ∣ z.2 := by
    intro z hz
    obtain ⟨hzR, hz₁, hz₂⟩ := Finset.mem_filter.mp hz
    exact ⟨diskFinset_mono _ _ (by positivity) (by linarith [Real.exp_pos t]) hzR, hz₁, hz₂⟩
  have hsum := lattice_mesh_log_weight_sum (Real.exp t) b (Real.exp_pos t) a ha hab haR
    (sourceUpperMesh t j) hZ
  change (∑ z ∈ sourceUpperMesh t j, sourceUpperMeshWeight t j z) ≤
    34 * (Real.exp t / (a : ℝ)) ^ 2 at hsum
  have hs : (Real.exp t / (a : ℝ)) ^ 2 ≤
      (D * ((j : ℝ) + 1) * Real.exp (j : ℝ)) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self
      (show 0 ≤ Real.exp t / (a : ℝ) by positivity) (hd j hj)
  calc
    _ ≤ 34 * (Real.exp t / (a : ℝ)) ^ 2 := hsum
    _ ≤ 34 * (D * ((j : ℝ) + 1) * Real.exp (j : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by
      rw [show 2 * (j : ℝ) = (j : ℝ) + j by ring, Real.exp_add]
      ring

end SRWTightness
