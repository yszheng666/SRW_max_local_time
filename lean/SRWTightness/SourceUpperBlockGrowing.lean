import SRWTightness.SourceUpperBlockForest
import SRWTightness.SourceSingleRootGeometry

namespace SRWTightness

/-- The actual upper forest uses exactly the geometric records in the comparison theorem. -/
theorem sourceUpperBlockForest_growing {M : Type*} (t : ℝ) (b : Site)
    (F : Site → PathWord → M) (ω : Sample) :
    sourceUpperBlockForest t b F ω =
      killedChildRecords (diskFinset (Real.exp t))
        (sourceUpperBlockInner t (sourceUpperBlockRoot t b) b)
        (sourceUpperBlockOuter t (sourceUpperBlockRoot t b) b) 0
        (actualFiniteWordRecord
          (growingRecordEntrance b (sourceUpperRadius t) (sourceUpperBuffer t))
          (growingRecordExit b (sourceUpperRadius t) (sourceUpperBuffer t))
          F (sourceUpperBlockForestDepth t b)) ω := by
  unfold sourceUpperBlockForest
  rw [source_actual_tree_growing (sourceUpperRadius t)
    (upperTerminalFineRadius (sourceUpperLogRadius t))
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) b F
    (sourceUpperBlockForestDepth t b) (Nat.sub_le _ _)]
  rfl

/-- The actual selected root's killing domain is the comparison tree's outer domain. -/
theorem sourceUpperBlockOuter_growing (t : ℝ) (b : Site)
    (hk : sourceUpperBlockRoot t b < sourceRootDepth (Real.exp t) (sourceUpperRadius t)) :
    sourceUpperBlockOuter t (sourceUpperBlockRoot t b) b =
      growingRecordExit b (sourceUpperRadius t) (sourceUpperBuffer t)
        (sourceUpperBlockForestDepth t b) :=
  source_single_root_exit (sourceUpperRadius t)
    (upperTerminalFineRadius (sourceUpperLogRadius t))
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (sourceUpperBlockRoot t b) hk b

end SRWTightness
