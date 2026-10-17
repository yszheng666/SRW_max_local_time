import SRWTightness.DiskCapacityLogBound
import SRWTightness.LatticeTranslation
import Mathlib.Analysis.Complex.ExponentialBounds

namespace SRWTightness

theorem capacity_energy_radius_bound (R a : ℝ) (ha : 1 ≤ a) (hRa : 2 * a ≤ R) :
    |1 / ((2 / Real.pi) * capacity (diskFinset R) (diskFinset a)) - Real.log (R / a)| ≤
      diskGreenEnergyConstant / (2 / Real.pi) := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hb := capacity_inverse_disk_log_bound R a ha hRa
  have hd := div_le_div_of_nonneg_right hb hg.le
  have he : 1 / ((2 / Real.pi) * capacity (diskFinset R) (diskFinset a)) - Real.log (R / a) =
      (1 / capacity (diskFinset R) (diskFinset a) - (2 / Real.pi) * Real.log (R / a)) / (2 / Real.pi) := by
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos hg]
  exact hd

theorem capacity_energy_translated_bound (b : Site) (R a : ℝ) (ha : 1 ≤ a) (hRa : 2 * a ≤ R) :
    |1 / ((2 / Real.pi) * capacity (translateFinset b (diskFinset R)) (translateFinset b (diskFinset a))) -
      Real.log (R / a)| ≤ diskGreenEnergyConstant / (2 / Real.pi) := by
  rw [capacity_translate]
  exact capacity_energy_radius_bound R a ha hRa

/-- Uniform energy estimate in the manuscript's killing radius `e*m + H`. -/
theorem capacity_energy_source_bound (b : Site) (m a H : ℝ) (ha : 1 ≤ a)
    (hma : 2 * a ≤ m) (hH : |H| ≤ m / 2) :
    |1 / ((2 / Real.pi) * capacity (translateFinset b (diskFinset (Real.exp 1 * m + H)))
        (translateFinset b (diskFinset a))) - (Real.log m - Real.log a)| ≤
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 := by
  have hm : 0 < m := by linarith
  have ha0 : 0 < a := by linarith
  have hHl := (abs_le.mp hH).1
  have hHu := (abs_le.mp hH).2
  have hRm : m ≤ Real.exp 1 * m + H := by nlinarith [Real.exp_one_gt_two]
  have hR4 : Real.exp 1 * m + H ≤ 4 * m := by nlinarith [Real.exp_one_lt_three]
  have hR : 0 < Real.exp 1 * m + H := by linarith
  have hb := capacity_energy_translated_bound b (Real.exp 1 * m + H) a ha (hma.trans hRm)
  have hrat0 : 1 ≤ (Real.exp 1 * m + H) / m := (le_div_iff₀ hm).mpr (by simpa using hRm)
  have hrat4 : (Real.exp 1 * m + H) / m ≤ 4 := (div_le_iff₀ hm).mpr hR4
  have hl0 : 0 ≤ Real.log ((Real.exp 1 * m + H) / m) := Real.log_nonneg hrat0
  have hl4 : Real.log ((Real.exp 1 * m + H) / m) ≤ Real.log 4 :=
    Real.log_le_log (by positivity) hrat4
  have he : 1 / ((2 / Real.pi) * capacity (translateFinset b (diskFinset (Real.exp 1 * m + H)))
        (translateFinset b (diskFinset a))) - (Real.log m - Real.log a) =
      (1 / ((2 / Real.pi) * capacity (translateFinset b (diskFinset (Real.exp 1 * m + H)))
        (translateFinset b (diskFinset a))) - Real.log ((Real.exp 1 * m + H) / a)) +
          Real.log ((Real.exp 1 * m + H) / m) := by
    rw [Real.log_div hR.ne' ha0.ne', Real.log_div hR.ne' hm.ne']
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hb (by simpa only [abs_of_nonneg hl0] using hl4))

end SRWTightness
