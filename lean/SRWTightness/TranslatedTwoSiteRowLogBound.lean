import SRWTightness.TwoSiteDiskRowLogBound
import SRWTightness.GreenTranslation

namespace SRWTightness

/-- Translating the disk preserves both discrete rows and their maximum. -/
theorem twoSiteDiscreteRowMax_translate (b : Site) (D : Finset Site) (z w : Site) :
    twoSiteDiscreteRowMax (translateFinset b D) (b + z) (b + w) =
      twoSiteDiscreteRowMax D z w := by
  simp only [twoSiteDiscreteRowMax, killedGreen_translate]

/-- The uniform logarithmic row bound for a disk centered at the first observed site. -/
theorem two_site_translated_row_log_bound (R : ℝ) (b w : Site)
    (hρ : 1 ≤ Real.sqrt (normSq (w - b)))
    (hR : 4 * Real.sqrt (normSq (w - b)) ≤ R) :
    |twoSiteDiscreteRowMax (translateFinset b (diskFinset R)) b w / (2 / Real.pi) -
      (2 * Real.log R - Real.log (Real.sqrt (normSq (w - b))))| ≤
      2 * (diskGreenEnergyConstant / (2 / Real.pi) + Real.log 2) + 1 / (2 / Real.pi) := by
  have he := twoSiteDiscreteRowMax_translate b (diskFinset R) 0 (w - b)
  rw [add_zero, show b + (w - b) = w by abel] at he
  rw [he]
  exact two_site_disk_row_log_bound R (w - b) hρ hR

end SRWTightness
