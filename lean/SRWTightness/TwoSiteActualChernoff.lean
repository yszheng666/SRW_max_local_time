import SRWTightness.TwoSiteDiscreteRow
import SRWTightness.TwoSiteRowChernoff

open MeasureTheory

namespace SRWTightness

/-- The two-point bound uses the actual maximum of the two discrete Green rows. -/
theorem two_site_actual_chernoff
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (D : Finset Site) (z w : Site) (hzw : z ≠ w) (hz : z ∈ D) (hw : w ∈ D)
    (α g W : ℝ) (hα : 0 ≤ α) (hg : 0 < g)
    (hcap : α * capacity D {z, w} ≤ 1) (hW : 0 ≤ W)
    (hsmall : twoSiteDiscreteRowMax D z w * W < 1)
    (u y : ℝ) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    (markProductLaw D {z, w} α k).real
      {Y | ∀ v : ({z, w} : Finset Site), g * y ^ 2 / 2 ≤ (sumMarks {z, w} k Y v : ℝ)} ≤
      Real.exp (-g * y ^ 2 * Real.log (1 + W) +
        α * u ^ 2 * W / (1 - twoSiteDiscreteRowMax D z w * W)) := by
  classical
  have hAD : ({z, w} : Finset Site) ⊆ D := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hcard : Fintype.card ({z, w} : Finset Site) = 2 := by simp [hzw]
  have hr := twoSiteDiscreteRowMax_nonneg D z w hz
  have he : g * (twoSiteDiscreteRowMax D z w / g) = twoSiteDiscreteRowMax D z w := by
    field_simp
  have hp := two_site_row_chernoff hOcc hRes D {z, w} hAD hcard α g
    (twoSiteDiscreteRowMax D z w / g) W hα hg.le (div_nonneg hr hg.le) hcap hW
    (by simpa only [he] using hsmall)
    (fun v ↦ by rw [he]; exact two_site_discrete_row_le D z w hzw v) u y k hk
  simpa only [he] using hp

end SRWTightness
