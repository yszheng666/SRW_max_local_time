import SRWTightness.SourceExcursionDomains
import SRWTightness.SourceUpperBlockBuffer
import SRWTightness.SourceUpperBlockRootGeometry

namespace SRWTightness

/-- Actual source block entrance domain A_(j+1), with the uniform buffer H0. -/
noncomputable def sourceUpperBlockInner (t : ℝ) (j : ℕ) (b : Site) : Finset Site :=
  translateFinset b (diskFinset (sourceUpperTraversalRadius t (j + 1) - sourceUpperBuffer t))

/-- Actual source block exit domain B_j, with the same uniform buffer H0. -/
noncomputable def sourceUpperBlockOuter (t : ℝ) (j : ℕ) (b : Site) : Finset Site :=
  translateFinset b (diskFinset (sourceUpperTraversalRadius t j + sourceUpperBuffer t))

/-- The actual upper entrance is the manuscript entrance domain at its exact source parameters. -/
theorem sourceUpperBlockInner_eq_sourceEntranceDomain (t : ℝ) (j : ℕ) (b : Site) :
    sourceUpperBlockInner t j b = sourceEntranceDomain (sourceUpperRadius t)
      (upperTerminalFineRadius (sourceUpperLogRadius t))
      (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) b j := rfl

/-- The actual upper exit is the manuscript exit domain at its exact source parameters. -/
theorem sourceUpperBlockOuter_eq_sourceExitDomain (t : ℝ) (j : ℕ) (b : Site) :
    sourceUpperBlockOuter t j b = sourceExitDomain (sourceUpperRadius t)
      (upperTerminalFineRadius (sourceUpperLogRadius t))
      (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) b j := rfl

end SRWTightness
