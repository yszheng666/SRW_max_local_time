import SRWTightness.SourceForwardStoppingComparison
import SRWTightness.WordFlatteningInternal

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- Literal source stopping-time traversals dominate actual forward counts of a nearby block. -/
theorem source_forward_count_le_stopped_traversal_internal
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
  exact_mod_cast source_forward_count_le_point_entrances two_level_word_flattening_input_internal m
    r ℓ k i hr hm hki hi b D
    hCD _ _ hK hKC hC x ω hfin

/-- The original walk's nearby-block count comparison holds almost surely with the infinite sum. -/
theorem source_forward_count_le_stopped_traversal_ae_internal
    (m r : ℝ) (ℓ k i : ℕ) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hki : k ≤ i) (hi : i + 1 ≤ ℓ) (b : Site) (D : Finset Site)
    (hCD : sourceExitDomain m r ℓ b k ⊆ D) (z : Site)
    (hnear : normSq (z - b) ≤ r ^ 2) (x : Site) :
    ∀ᵐ ω ∂pathLaw, (sourceForwardRecordCount m r ℓ k i b D x ω : ℝ≥0∞) ≤
      sourceTraversalStoppedCount D
        (translateFinset z (diskFinset (sourceRecordRadius m ℓ (i + 1))))
        (translateFinset z (diskFinset (sourceRecordRadius m ℓ i))) x ω := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hfin
  exact source_forward_count_le_stopped_traversal_internal
    m r ℓ k i hr hm hki hi b D
    hCD z hnear x ω hfin

end SRWTightness
