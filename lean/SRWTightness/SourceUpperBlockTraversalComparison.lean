import SRWTightness.SourceUpperBlockDirectCount
import SRWTightness.SourceUpperTraversalComparison

open Filter MeasureTheory

namespace SRWTightness

/-- Buffered block traversals are dominated by point-centered traversals at every block site. -/
theorem source_upper_block_direct_count_le_point (t : ℝ) (j : ℕ) (b x : Site)
    (hx : x ∈ sourceUpperBlock t b)
    (hr : sourceUpperBuffer t ≤ sourceUpperTraversalRadius t (j + 1)) (ω : Sample) :
    (killedChildIntervals (diskFinset (Real.exp t)) (sourceUpperBlockInner t j b)
      (sourceUpperBlockOuter t j b) 0 ω).length ≤ sourceUpperTraversalCount t j x ω := by
  have ha : (sourceUpperBlockSide t : ℝ) ≤ sourceUpperBuffer t := by
    rw [sourceUpperBlockSide_cast]
    unfold sourceUpperBuffer
    have h : 0 ≤ upperTerminalFineRadius (sourceUpperLogRadius t) := by
      unfold upperTerminalFineRadius
      positivity
    linarith
  have hn := centeredLatticeBlock_near (sourceUpperBlockSide t) b x hx
  have hsym : normSq (b - x) ≤ (sourceUpperBlockSide t : ℝ) ^ 2 := by
    simpa only [show b - x = -(x - b) by abel, normSq_neg] using hn
  have hr0 : 0 ≤ sourceUpperTraversalRadius t (j + 1) := by
    unfold sourceUpperTraversalRadius sourceRecordRadius sourceUpperRadius
    positivity
  have hK : sourceUpperBlockInner t j b ⊆
      translateFinset x (diskFinset (sourceUpperTraversalRadius t (j + 1))) :=
    translated_disk_subset_of_displacement b x (sourceUpperBlockSide t : ℝ) _ _
      (Nat.cast_nonneg _) (sub_nonneg.mpr hr) hsym (by linarith)
  have hC : translateFinset x (diskFinset (sourceUpperTraversalRadius t j)) ⊆
      sourceUpperBlockOuter t j b :=
    translated_disk_subset_of_displacement x b (sourceUpperBlockSide t : ℝ) _ _
      (Nat.cast_nonneg _) (by
        unfold sourceUpperTraversalRadius sourceRecordRadius sourceUpperRadius
        positivity) hn (by linarith)
  have he := sourceRecordRadius_successor (sourceUpperRadius t)
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) j
  have hKC : translateFinset x (diskFinset (sourceUpperTraversalRadius t (j + 1))) ⊆
      translateFinset x (diskFinset (sourceUpperTraversalRadius t j)) := by
    apply Finset.image_subset_image
    apply diskFinset_mono _ _ hr0
    change Real.exp 1 * sourceUpperTraversalRadius t (j + 1) =
      sourceUpperTraversalRadius t j at he
    nlinarith [Real.exp_one_gt_two]
  exact killedChildIntervals_length_mono _ _ _ _ _ hK hKC hC 0 ω

/-- Actual forward block counts are almost surely below every block site's traversal counts. -/
theorem source_upper_block_count_le_point_ae (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t, ∀ᵐ ω ∂pathLaw,
      ∀ j : ℕ, sourceUpperBlockRoot t b ≤ j → j ≤ sourceUpperCoarseDepth t →
      ∀ x ∈ sourceUpperBlock t b,
        sourceUpperBlockCount t b j ω ≤ sourceUpperTraversalCount t j x ω := by
  filter_upwards [source_upper_block_count_eq_direct_ae hF,
    source_upper_block_observation_conditions, source_upper_block_root_lt_depth]
    with t hd ho hk
  intro b hb
  filter_upwards [hd b hb] with ω hω
  intro j hj hJ x hx
  rw [hω j hj hJ]
  apply source_upper_block_direct_count_le_point t j b x hx
  have hrad := sourceRecordRadius_ge_terminal (sourceUpperRadius t)
    (Real.exp_pos _).le (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (j + 1) (by
      have := hk b hb
      change j ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) - 1 at hJ
      omega)
  change sourceUpperRadius t ≤ sourceUpperTraversalRadius t (j + 1) at hrad
  linarith [ho.1]

end SRWTightness
