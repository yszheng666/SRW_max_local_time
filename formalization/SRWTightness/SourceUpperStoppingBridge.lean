import SRWTightness.SourceTraversalStoppedCount
import SRWTightness.SourceUpperTraversalComparison

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The unbuffered source point shells are nested at every level. -/
theorem source_upper_point_shells_nested (t : ℝ) (j : ℕ) (x : Site) :
    translateFinset x (diskFinset (sourceUpperTraversalRadius t (j + 1))) ⊆
      translateFinset x (diskFinset (sourceUpperTraversalRadius t j)) := by
  apply Finset.image_subset_image
  apply diskFinset_mono
  · unfold sourceUpperTraversalRadius sourceRecordRadius sourceUpperRadius
    positivity
  · exact sourceRecordRadius_antitone (sourceUpperRadius t) (Real.exp_pos _).le
      (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (Nat.le_succ j)

/-- Actual upper traversal counts equal the literal source stopping sum on a finite killed path. -/
theorem source_upper_traversal_count_eq_stopped (t : ℝ) (j : ℕ) (x : Site) (ω : Sample)
    (hC : translateFinset x (diskFinset (sourceUpperTraversalRadius t j)) ⊆
      diskFinset (Real.exp t)) (hfin : domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤) :
    (sourceUpperTraversalCount t j x ω : ℝ≥0∞) =
      sourceTraversalStoppedCount (diskFinset (Real.exp t))
        (translateFinset x (diskFinset (sourceUpperTraversalRadius t (j + 1))))
        (translateFinset x (diskFinset (sourceUpperTraversalRadius t j))) 0 ω := by
  symm
  exact sourceTraversalStoppedCount_eq_complete _ _ _ (source_upper_point_shells_nested t j x)
    hC 0 ω hfin

/-- One almost-sure set identifies all inner-disk upper counts with the manuscript's
infinite sum. -/
theorem source_upper_traversal_count_eq_stopped_ae (t : ℝ)
    (hR : 32 * sourceUpperRadius t ≤ Real.exp t) :
    ∀ᵐ ω ∂pathLaw, ∀ j : ℕ, ∀ x ∈ diskFinset (Real.exp t / 2),
      (sourceUpperTraversalCount t j x ω : ℝ≥0∞) =
        sourceTraversalStoppedCount (diskFinset (Real.exp t))
          (translateFinset x (diskFinset (sourceUpperTraversalRadius t (j + 1))))
          (translateFinset x (diskFinset (sourceUpperTraversalRadius t j))) 0 ω := by
  filter_upwards [domainExit_ne_top_ae (diskFinset (Real.exp t)) 0] with ω hfin
  intro j x hx
  exact source_upper_traversal_count_eq_stopped t j x ω
    (source_upper_traversal_outer_subset_killing t j x hR hx) hfin

end SRWTightness
