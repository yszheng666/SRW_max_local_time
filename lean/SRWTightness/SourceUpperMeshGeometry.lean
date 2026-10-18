import SRWTightness.SourceUpperMeshCount
import SRWTightness.TranslatedDiskContainment

namespace SRWTightness

/-- The mesh buffer is smaller than half the fine radius once that radius is at least ten. -/
theorem source_upper_mesh_buffer_bound (t : ℝ) (j : ℕ)
    (hr : 10 ≤ sourceUpperTraversalRadius t (j + 1)) :
    0 ≤ sourceUpperMeshBuffer t j ∧
      2 * sourceUpperMeshBuffer t j ≤ sourceUpperTraversalRadius t (j + 1) := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hd : 0 < 1000 * ((j : ℝ) + 1) := by positivity
  have hfloor : (sourceUpperMeshSpacing t j : ℝ) ≤
      sourceUpperTraversalRadius t (j + 1) / (1000 * ((j : ℝ) + 1)) :=
    Nat.floor_le (by positivity)
  have hf := (le_div_iff₀ hd).mp hfloor
  have ha : 0 ≤ (sourceUpperMeshSpacing t j : ℝ) := Nat.cast_nonneg _
  unfold sourceUpperMeshBuffer
  constructor
  · positivity
  · nlinarith [mul_nonneg ha hj]

/-- The upper mesh inner disk is contained in its outer disk at the explicit radius threshold. -/
theorem source_upper_mesh_inner_subset_outer (t : ℝ) (j : ℕ) (z : Site)
    (hr : 10 ≤ sourceUpperTraversalRadius t (j + 1)) :
    sourceUpperMeshInner t j z ⊆ sourceUpperMeshOuter t j z := by
  have hb := source_upper_mesh_buffer_bound t j hr
  have he : Real.exp 1 * sourceUpperTraversalRadius t (j + 1) =
      sourceUpperTraversalRadius t j := sourceRecordRadius_successor _ _ j
  have hgap : sourceUpperTraversalRadius t (j + 1) + sourceUpperMeshBuffer t j ≤
      sourceUpperTraversalRadius t j - sourceUpperMeshBuffer t j := by
    nlinarith [Real.exp_one_gt_two]
  intro y hy
  apply (mem_translateFinset_iff z _ y).mpr
  exact diskFinset_mono _ _ (by linarith) hgap ((mem_translateFinset_iff z _ y).mp hy)

/-- Nearby observation centers have their inner traversal disk inside the upper mesh inner disk. -/
theorem source_upper_mesh_inner_cover (t : ℝ) (j : ℕ) (x z : Site)
    (hnear : normSq (x - z) ≤ (sourceUpperMeshSpacing t j : ℝ) ^ 2) :
    translateFinset x (diskFinset (sourceUpperTraversalRadius t (j + 1))) ⊆
      sourceUpperMeshInner t j z := by
  have hr0 : 0 ≤ sourceUpperTraversalRadius t (j + 1) := by
    unfold sourceUpperTraversalRadius sourceRecordRadius sourceUpperRadius
    positivity
  apply translated_disk_subset_of_displacement x z (sourceUpperMeshSpacing t j : ℝ)
    _ _ (Nat.cast_nonneg _) hr0 hnear
  unfold sourceUpperMeshBuffer
  have ha : 0 ≤ (sourceUpperMeshSpacing t j : ℝ) := Nat.cast_nonneg _
  linarith

/-- A mesh outer disk is inside the point-centered unbuffered traversal disk. -/
theorem source_upper_mesh_outer_cover (t : ℝ) (j : ℕ) (x z : Site)
    (hr : 10 ≤ sourceUpperTraversalRadius t (j + 1))
    (hnear : normSq (x - z) ≤ (sourceUpperMeshSpacing t j : ℝ) ^ 2) :
    sourceUpperMeshOuter t j z ⊆
      translateFinset x (diskFinset (sourceUpperTraversalRadius t j)) := by
  have hb := source_upper_mesh_buffer_bound t j hr
  have he : Real.exp 1 * sourceUpperTraversalRadius t (j + 1) =
      sourceUpperTraversalRadius t j := sourceRecordRadius_successor _ _ j
  have hsym : normSq (z - x) ≤ (sourceUpperMeshSpacing t j : ℝ) ^ 2 := by
    simpa only [show z - x = -(x - z) by abel, normSq_neg] using hnear
  have hr0 : 0 ≤ sourceUpperTraversalRadius t j - sourceUpperMeshBuffer t j := by
    nlinarith [Real.exp_one_gt_two]
  apply translated_disk_subset_of_displacement z x (sourceUpperMeshSpacing t j : ℝ)
    _ _ (Nat.cast_nonneg _) hr0 hsym
  unfold sourceUpperMeshBuffer
  have ha : 0 ≤ (sourceUpperMeshSpacing t j : ℝ) := Nat.cast_nonneg _
  linarith

end SRWTightness
