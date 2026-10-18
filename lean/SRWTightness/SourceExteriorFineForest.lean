import SRWTightness.ExteriorWordAlignment
import SRWTightness.SourceGroupedFineError
import SRWTightness.SourceOriginalJointRootBound

namespace SRWTightness

/-- The fixed header/word data on an actual exterior fiber reconstruct the original grouped fine forest. -/
theorem source_exterior_fine_forest (t : ℝ) (b w z : Site) (Kobs : Finset Site)
    (ν J : ℕ) (ω : Sample) (h : ExteriorPathRecord) (us : List PathWord)
    (hh : sourcePairExteriorRecord t b w ν J ω = h)
    (hu : killedChildRecords (diskFinset (Real.exp t))
      (sourceEntranceDomain (sourceLowerRadius t) 1
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν ∪
        sourceEntranceDomain (sourceLowerRadius t) 1
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) w ν)
      (sourceExitDomain (sourceLowerRadius t) 1
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b (ν - J) ∪
        sourceExitDomain (sourceLowerRadius t) 1
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) w (ν - J))
      0 (fun _ u ↦ u) ω = us) :
    (h.1.zip us).flatMap (fun p ↦ wordChildRecords
      (sourceEntranceDomain (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν)
      (sourceExitDomain (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν)
      p.1.2.2.1 (sourceLongFineRecord t z Kobs ν) p.2) =
        sourceGroupedFineForest t b w z Kobs ν J ω := by
  have he := exterior_word_fiber_records _ _ _ _ 0 ω h us hh hu
    (fun y u ↦ wordChildRecords
      (sourceEntranceDomain (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν)
      (sourceExitDomain (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν)
      y (sourceLongFineRecord t z Kobs ν) u)
  exact congrArg List.flatten he

end SRWTightness
