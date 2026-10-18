import SRWTightness.StoppedWordProbabilityInternal

open MeasureTheory
namespace SRWTightness

/-- An admissible finite word gives a strictly positive probability of its prescribed exit. -/
theorem admissibleExitWord_exit_positive (C : Finset Site) (x e : Site) (w : PathWord)
    (hw : AdmissibleExitWord C x e w) : 0 < traceExitProbability C x e := by
  have hp : 0 < pathLaw.real {ω | killedPathWord C x ω = w} := by
    rw [stoppedWordProbabilityInput_internal C x e w hw]
    positivity
  apply hp.trans_le
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  change domainExitLocation C x ω = e
  rw [← killedPathWord_exitLocation C x ω, show killedPathWord C x ω = w from hω]
  exact hw.2.1

end SRWTightness
