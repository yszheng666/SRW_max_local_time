import SRWTightness.SourceTraversalStoppedCount
import SRWTightness.SourceForwardEntranceComparison
import SRWTightness.TranslatedDiskContainment

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- A nearby point's unbuffered inner and outer shells satisfy the source injection geometry. -/
theorem source_point_shell_inclusions (m r : ℝ) (ℓ i : ℕ) (b z : Site)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m) (hi : i + 1 ≤ ℓ)
    (hnear : normSq (z - b) ≤ r ^ 2) :
    sourceEntranceDomain m r ℓ b i ⊆
        translateFinset z (diskFinset (sourceRecordRadius m ℓ (i + 1))) ∧
      (translateFinset z (diskFinset (sourceRecordRadius m ℓ (i + 1))) ⊆
        translateFinset z (diskFinset (sourceRecordRadius m ℓ i))) ∧
      (translateFinset z (diskFinset (sourceRecordRadius m ℓ i)) ⊆
        sourceExitDomain m r ℓ b i) := by
  have hH : r ≤ sourceRecordBuffer r := by unfold sourceRecordBuffer; linarith
  have hm0 : 0 ≤ m := by unfold sourceRecordBuffer at hm; linarith
  have hsmall := sourceRecordRadius_ge_terminal m hm0 ℓ (i + 1) hi
  have hlarge : 0 ≤ sourceRecordRadius m ℓ i := by
    unfold sourceRecordRadius
    positivity
  have hsym : normSq (b - z) ≤ r ^ 2 := by
    simpa only [show b - z = -(z - b) by abel, normSq_neg] using hnear
  refine ⟨?_, ?_, ?_⟩
  · exact translated_disk_subset_of_displacement b z r _ _ hr (by linarith) hsym
      (by linarith)
  · apply Finset.image_subset_image
    exact diskFinset_mono _ _ (by linarith)
      (sourceRecordRadius_antitone m hm0 ℓ (Nat.le_succ i))
  · exact translated_disk_subset_of_displacement z b r _ _ hr hlarge hnear (by linarith)

/-- Literal source stopping-time traversals dominate actual forward counts of a nearby block. -/
theorem source_forward_count_le_stopped_traversal (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ k i : ℕ) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hki : k ≤ i) (hi : i + 1 ≤ ℓ) (b : Site) (D : Finset Site)
    (hCD : sourceExitDomain m r ℓ b k ⊆ D) (z : Site)
    (hnear : normSq (z - b) ≤ r ^ 2) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) :
    (sourceForwardRecordCount m r ℓ k i b D x ω : ℝ≥0∞) ≤
      sourceTraversalStoppedCount D
        (translateFinset z (diskFinset (sourceRecordRadius m ℓ (i + 1))))
        (translateFinset z (diskFinset (sourceRecordRadius m ℓ i))) x ω := by
  obtain ⟨hK, hKC, hC⟩ := source_point_shell_inclusions m r ℓ i b z hr hm hi hnear
  rw [sourceTraversalStoppedCount_eq_entrances D _ _ hKC x ω hfin]
  exact_mod_cast source_forward_count_le_point_entrances hF m r ℓ k i hr hm hki hi b D
    hCD _ _ hK hKC hC x ω hfin

/-- The original walk's nearby-block count comparison holds almost surely with the infinite sum. -/
theorem source_forward_count_le_stopped_traversal_ae (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ k i : ℕ) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hki : k ≤ i) (hi : i + 1 ≤ ℓ) (b : Site) (D : Finset Site)
    (hCD : sourceExitDomain m r ℓ b k ⊆ D) (z : Site)
    (hnear : normSq (z - b) ≤ r ^ 2) (x : Site) :
    ∀ᵐ ω ∂pathLaw, (sourceForwardRecordCount m r ℓ k i b D x ω : ℝ≥0∞) ≤
      sourceTraversalStoppedCount D
        (translateFinset z (diskFinset (sourceRecordRadius m ℓ (i + 1))))
        (translateFinset z (diskFinset (sourceRecordRadius m ℓ i))) x ω := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hfin
  exact source_forward_count_le_stopped_traversal hF m r ℓ k i hr hm hki hi b D
    hCD z hnear x ω hfin

end SRWTightness
