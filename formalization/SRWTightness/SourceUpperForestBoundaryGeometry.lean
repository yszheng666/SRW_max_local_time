import SRWTightness.SourceUpperBlockDomainGeometry
import SRWTightness.SourceUpperActualForestError
import SRWTightness.RootOuterDomainGeometry

open Filter

namespace SRWTightness

/-- Actual selected upper roots satisfy the entrance support and full exit-boundary conditions. -/
theorem source_upper_forest_boundary_geometry :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      1 ≤ sourceUpperTraversalRadius t (sourceUpperBlockRoot t b + 1) - sourceUpperBuffer t ∧
      domainExitBoundary (sourceUpperBlockOuter t (sourceUpperBlockRoot t b) b) ⊆
        (diskFinset (Real.exp t) : Set Site) ∧
      (0 : Site) ∈ diskFinset (Real.exp t) \
        sourceUpperBlockInner t (sourceUpperBlockRoot t b) b := by
  filter_upwards [source_upper_block_relative_buffer, source_upper_mesh_scale_conditions,
    source_upper_block_root_coarse_range, source_upper_block_center_distance,
    source_upper_block_root_conditions, eventually_ge_atTop (16 : ℝ)]
    with t hbuf hs hk hdist hroot ht16
  intro b hb
  let k := sourceUpperBlockRoot t b
  let r := sourceUpperTraversalRadius t (k + 1)
  let H := sourceUpperBuffer t
  let c := sourceUpperTraversalRadius t k + H
  have hkn : k ≤ sourceUpperCoarseDepth t := hk b hb
  have hr10 : 10 ≤ r := (hs.2 k hkn).1
  have hH : 0 ≤ H := by dsimp [H]; unfold sourceUpperBuffer upperTerminalFineRadius; positivity
  have hsmall := hbuf k hkn
  change H ≤ r / (200 * ((k : ℝ) + 1)) at hsmall
  have hhalf : 2 * H ≤ r := by
    have h := (le_div_iff₀ (by positivity : 0 < 200 * ((k : ℝ) + 1))).mp hsmall
    nlinarith [mul_nonneg hH (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have ha : 1 ≤ r - H := by linarith
  have he : Real.exp 1 * r = sourceUpperTraversalRadius t k :=
    sourceRecordRadius_successor _ _ k
  have hrle : r ≤ sourceUpperTraversalRadius t k := by nlinarith [Real.exp_one_gt_two]
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hrad := source_upper_traversal_radius_bound t hs.1 k
  change 32 * sourceUpperTraversalRadius t k ≤ Real.exp t at hrad
  have hfit : Real.sqrt (normSq b) + c + 1 < Real.exp t := by
    have hd := (hdist b hb).2
    have hR := Real.add_one_le_exp t
    dsimp [c]
    linarith
  have hboundary := (root_domain_and_exit_inside b c (Real.exp t) hc hfit).2
  have hnot : (0 : Site) ∉ sourceUpperBlockInner t k b := by
    intro hz
    have hsub : sourceUpperBlockInner t k b ⊆
        translateFinset b (diskFinset (r + H)) :=
      Finset.image_subset_image (diskFinset_mono (r - H) (r + H)
        (by linarith) (by linarith))
    exact (hroot b hb).2.2.2 (k + 1) le_rfl (hsub hz)
  exact ⟨ha, hboundary, Finset.mem_sdiff.mpr
    ⟨zero_mem_diskFinset _ (Real.exp_pos _), hnot⟩⟩

end SRWTightness
