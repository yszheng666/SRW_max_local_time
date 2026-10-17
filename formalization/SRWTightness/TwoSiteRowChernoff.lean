import SRWTightness.MarkSumRowChernoff
import SRWTightness.ObservationGreenRowNonnegative

open MeasureTheory

namespace SRWTightness

/-- The two-site common-mark bound with the manuscript occupation and population normalization. -/
theorem two_site_row_chernoff
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (D A : Finset Site) (hAD : A ⊆ D) (hcard : Fintype.card A = 2)
    (α g Dj W : ℝ) (hα : 0 ≤ α) (hg : 0 ≤ g) (hDj : 0 ≤ Dj)
    (hcap : α * capacity D A ≤ 1) (hW : 0 ≤ W) (hsmall : g * Dj * W < 1)
    (hrow : ∀ v : A, (∑ v' : A, (killedGreen D v v' - (if v = v' then 1 else 0))) ≤ g * Dj)
    (u y : ℝ) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    (markProductLaw D A α k).real {Y | ∀ v : A, g * y ^ 2 / 2 ≤ (sumMarks A k Y v : ℝ)} ≤
      Real.exp (-g * y ^ 2 * Real.log (1 + W) + α * u ^ 2 * W / (1 - g * Dj * W)) := by
  have hr (v : A) : (∑ v' : A, |killedGreen D v v' - (if v = v' then 1 else 0)|) ≤ g * Dj := by
    rw [observationGreen_sub_one_abs_row D A hAD v]
    exact hrow v
  have hp := markSum_all_high_row_bound hOcc hRes D A hAD α hα hcap (g * Dj) W
    (mul_nonneg hg hDj) hW hsmall hr k (g * y ^ 2 / 2)
  rw [hcard] at hp
  push_cast at hp
  calc
    _ ≤ Real.exp (-(2 : ℝ) * (g * y ^ 2 / 2) * Real.log (1 + W) +
        α * 2 * k * W / (1 - g * Dj * W)) := hp
    _ = _ := by
      rw [← hk]
      congr 1
      ring

end SRWTightness
