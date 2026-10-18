import SRWTightness.LatticeTranslation

namespace SRWTightness

theorem domainSteps_translate (b : Site) (D : Finset Site) (x : Site) (ω : Sample) :
    domainSteps (translateFinset b D) (b + x) ω = domainSteps D x ω := by
  simp only [domainSteps, domainExit_translate]

theorem domainLocalTime_translate (b : Site) (D : Finset Site) (x y : Site) (ω : Sample) :
    domainLocalTime (translateFinset b D) (b + x) (b + y) ω = domainLocalTime D x y ω := by
  simp only [domainLocalTime, domainSteps_translate]
  congr 1
  abel

theorem killedGreen_translate (b : Site) (D : Finset Site) (x y : Site) :
    killedGreen (translateFinset b D) (b + x) (b + y) = killedGreen D x y := by
  simp only [killedGreen, domainLocalTime_translate]

end SRWTightness
