import SRWTightness.SourceUpperMeshScale
import SRWTightness.WordChildCountMonotone
import SRWTightness.LatticeMeshNearest

open Filter

namespace SRWTightness

/-- Complete unbuffered point-centered traversals at the actual upper source scale. -/
noncomputable def sourceUpperTraversalCount (t : ℝ) (j : ℕ) (x : Site) (ω : Sample) : ℕ :=
  (killedChildIntervals (diskFinset (Real.exp t))
    (translateFinset x (diskFinset (sourceUpperTraversalRadius t (j + 1))))
    (translateFinset x (diskFinset (sourceUpperTraversalRadius t j))) 0 ω).length

/-- Every nearby point-centered complete traversal is dominated by the actual mesh count. -/
theorem source_upper_traversal_count_le_mesh (t : ℝ) (j : ℕ) (x z : Site)
    (hr : 10 ≤ sourceUpperTraversalRadius t (j + 1))
    (hnear : normSq (x - z) ≤ (sourceUpperMeshSpacing t j : ℝ) ^ 2) (ω : Sample) :
    sourceUpperTraversalCount t j x ω ≤ sourceUpperMeshCount t j z ω :=
  killedChildIntervals_length_mono _ _ _ _ _ (source_upper_mesh_inner_cover t j x z hnear)
    (source_upper_mesh_inner_subset_outer t j z hr)
    (source_upper_mesh_outer_cover t j x z hr hnear) 0 ω

/-- Every upper traversal radius is bounded by the root radius selected in the manuscript. -/
theorem source_upper_traversal_radius_bound (t : ℝ)
    (hR : 32 * sourceUpperRadius t ≤ Real.exp t) (j : ℕ) :
    32 * sourceUpperTraversalRadius t j ≤ Real.exp t := by
  have hm : 0 < sourceUpperRadius t := Real.exp_pos _
  have hmono := sourceRecordRadius_antitone (sourceUpperRadius t) hm.le
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (Nat.zero_le j)
  have hroot := (source_root_depth_bracket (Real.exp t) (sourceUpperRadius t) hm hR).1
  change sourceUpperTraversalRadius t j ≤ sourceUpperTraversalRadius t 0 at hmono
  change 32 * sourceUpperTraversalRadius t 0 ≤ Real.exp t at hroot
  linarith

/-- Upper mesh outer disks lie inside the actual killing domain. -/
theorem source_upper_mesh_outer_subset_killing (t : ℝ) (j : ℕ) (z : Site)
    (hR : 32 * sourceUpperRadius t ≤ Real.exp t)
    (hr : 10 ≤ sourceUpperTraversalRadius t (j + 1)) (hz : z ∈ sourceUpperMesh t j) :
    sourceUpperMeshOuter t j z ⊆ diskFinset (Real.exp t) := by
  have hb := source_upper_mesh_buffer_bound t j hr
  have he : Real.exp 1 * sourceUpperTraversalRadius t (j + 1) =
      sourceUpperTraversalRadius t j := sourceRecordRadius_successor _ _ j
  have hout : 0 ≤ sourceUpperTraversalRadius t j - sourceUpperMeshBuffer t j := by
    nlinarith [Real.exp_one_gt_two]
  have hrad := source_upper_traversal_radius_bound t hR j
  have hz' : normSq z ≤ (3 * Real.exp t / 4) ^ 2 :=
    ((mem_diskFinset _ _).mp (Finset.mem_filter.mp hz).1).le
  have h := translated_disk_subset_of_displacement z 0 (3 * Real.exp t / 4)
    (sourceUpperTraversalRadius t j - sourceUpperMeshBuffer t j) (Real.exp t)
    (by positivity) hout (by simpa only [sub_zero] using hz') (by linarith)
  simpa only [sourceUpperMeshOuter, translateFinset, zero_add, Finset.image_id'] using h

/-- Point-centered upper traversal disks lie inside the actual killing domain. -/
theorem source_upper_traversal_outer_subset_killing (t : ℝ) (j : ℕ) (x : Site)
    (hR : 32 * sourceUpperRadius t ≤ Real.exp t)
    (hx : x ∈ diskFinset (Real.exp t / 2)) :
    translateFinset x (diskFinset (sourceUpperTraversalRadius t j)) ⊆
      diskFinset (Real.exp t) := by
  have hrad := source_upper_traversal_radius_bound t hR j
  have hr : 0 ≤ sourceUpperTraversalRadius t j := by
    unfold sourceUpperTraversalRadius sourceRecordRadius sourceUpperRadius
    positivity
  have hx' : normSq x ≤ (Real.exp t / 2) ^ 2 := ((mem_diskFinset _ _).mp hx).le
  have h := translated_disk_subset_of_displacement x 0 (Real.exp t / 2)
    (sourceUpperTraversalRadius t j) (Real.exp t) (by positivity) hr
    (by simpa only [sub_zero] using hx') (by linarith)
  simpa only [translateFinset, zero_add, Finset.image_id'] using h

/-- The actual source mesh eventually supplies the pathwise comparison at all coarse levels. -/
theorem source_upper_traversal_mesh_comparison :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t →
      ∀ x ∈ diskFinset (Real.exp t / 2), ∃ z ∈ sourceUpperMesh t j,
        normSq (x - z) ≤ (sourceUpperMeshSpacing t j : ℝ) ^ 2 ∧
        sourceUpperMeshOuter t j z ⊆ diskFinset (Real.exp t) ∧
        (translateFinset x (diskFinset (sourceUpperTraversalRadius t j)) ⊆
          diskFinset (Real.exp t)) ∧
        ∀ ω : Sample, sourceUpperTraversalCount t j x ω ≤ sourceUpperMeshCount t j z ω := by
  filter_upwards [source_upper_mesh_scale_conditions] with t ht
  intro j hj x hx
  obtain ⟨hr, ha, haR⟩ := ht.2 j hj
  obtain ⟨z, hz, hz₁, hz₂, hnear⟩ :=
    lattice_mesh_near_in_disk (Real.exp t) (Real.exp_pos t) _ ha haR x hx
  have hzmesh : z ∈ sourceUpperMesh t j := Finset.mem_filter.mpr ⟨hz, hz₁, hz₂⟩
  exact ⟨z, hzmesh, hnear, source_upper_mesh_outer_subset_killing t j z ht.1 hr hzmesh,
    source_upper_traversal_outer_subset_killing t j x ht.1 hx,
    source_upper_traversal_count_le_mesh t j x z hr hnear⟩

end SRWTightness
