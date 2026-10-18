import SRWTightness.SourceUpperBlockDomains

open Filter

namespace SRWTightness

/-- Actual block entrance and exit domains are nested and contained in the killing disk. -/
theorem source_upper_block_domain_geometry :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t →
      ∀ b ∈ sourceUpperBlockCenters t,
        sourceUpperBlockInner t j b ⊆ sourceUpperBlockOuter t j b ∧
        sourceUpperBlockOuter t j b ⊆ diskFinset (Real.exp t) := by
  filter_upwards [source_upper_block_relative_buffer, source_upper_mesh_scale_conditions,
    source_upper_block_center_distance] with t hs ht hb
  intro j hj b hbcen
  let r := sourceUpperTraversalRadius t (j + 1)
  let H := sourceUpperBuffer t
  let c := sourceUpperTraversalRadius t j + H
  have hr : 0 < r := by have h := (ht.2 j hj).1; dsimp [r]; linarith
  have hH : 0 ≤ H := by dsimp [H]; unfold sourceUpperBuffer upperTerminalFineRadius; positivity
  have hsmall := hs j hj
  change H ≤ r / (200 * ((j : ℝ) + 1)) at hsmall
  have hhalf : 2 * H ≤ r := by
    have h := (le_div_iff₀ (by positivity : 0 < 200 * ((j : ℝ) + 1))).mp hsmall
    nlinarith [mul_nonneg hH (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have he : Real.exp 1 * r = sourceUpperTraversalRadius t j :=
    sourceRecordRadius_successor _ _ j
  have hrc : r - H ≤ c := by dsimp [c]; nlinarith [Real.exp_one_gt_two]
  have hc : 0 ≤ c := by linarith
  constructor
  · intro x hx
    apply (mem_translateFinset_iff b _ x).mpr
    exact diskFinset_mono (r - H) c (by linarith) hrc
      ((mem_translateFinset_iff b _ x).mp hx)
  · have hbnd : normSq b ≤ (3 * Real.exp t / 4) ^ 2 := by
      have h := (hb b hbcen).2
      nlinarith [Real.sq_sqrt (normSq_nonneg b), Real.sqrt_nonneg (normSq b)]
    have hrad := source_upper_traversal_radius_bound t ht.1 j
    have hrle : r ≤ sourceUpperTraversalRadius t j := by
      nlinarith [Real.exp_one_gt_two]
    change 32 * sourceUpperTraversalRadius t j ≤ Real.exp t at hrad
    have h := translated_disk_subset_of_displacement b 0 (3 * Real.exp t / 4) c
      (Real.exp t) (by positivity) hc (by simpa only [sub_zero] using hbnd)
      (by dsimp [c]; linarith [Real.exp_pos t])
    simpa only [sourceUpperBlockOuter, c, H, translateFinset, zero_add, Finset.image_id'] using h

end SRWTightness
