import SRWTightness.TwoSiteDiscreteRow
import SRWTightness.PairGreenLogDistance
import SRWTightness.DiskDiagonalLogBound
import SRWTightness.GreenSymmetry

namespace SRWTightness

/-- The discrete two-site row scale retains a uniform logarithmic error, including minus one. -/
theorem two_site_disk_row_log_bound (R : ℝ) (w : Site)
    (hρ : 1 ≤ Real.sqrt (normSq w)) (hR : 4 * Real.sqrt (normSq w) ≤ R) :
    |twoSiteDiscreteRowMax (diskFinset R) 0 w / (2 / Real.pi) -
      (2 * Real.log R - Real.log (Real.sqrt (normSq w)))| ≤
      2 * (diskGreenEnergyConstant / (2 / Real.pi) + Real.log 2) + 1 / (2 / Real.pi) := by
  let g : ℝ := 2 / Real.pi
  let E := diskGreenEnergyConstant / g + Real.log 2
  have hg : 0 < g := by dsimp [g]; positivity
  have hr : 0 < Real.sqrt (normSq w) := by linarith
  have hR4 : 4 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hs := Real.sq_sqrt (normSq_nonneg w)
  have hw : w ∈ diskFinset R := by
    rw [mem_diskFinset]
    change normSq w < R ^ 2
    nlinarith
  have h0 : (0 : Site) ∈ diskFinset R := by
    rw [mem_diskFinset]
    change normSq (0 : Site) < R ^ 2
    simpa [normSq] using sq_pos_of_pos hR0
  have hdiagw := abs_le.mp (diskGreen_diagonal_interior_log_bound R hR4 w (by nlinarith))
  have hdiag0 := abs_le.mp (diskGreen_diagonal_interior_log_bound R hR4 0 (by
    simpa [normSq] using sq_nonneg (R / 2)))
  have hcross := abs_le.mp (diskGreen_pair_log_distance R w hρ hR)
  rw [Real.log_div hR0.ne' hr.ne'] at hcross
  have hsym := killedGreen_symm (diskFinset R) w 0 hw h0
  have hEg : E * g = diskGreenEnergyConstant + g * Real.log 2 := by
    dsimp [E]
    field_simp
  have hdiag (x : Site)
      (hd : -(diskGreenEnergyConstant + g * Real.log 2) ≤ diskGreen R x x - g * Real.log R ∧
        diskGreen R x x - g * Real.log R ≤ diskGreenEnergyConstant + g * Real.log 2) :
      Real.log R - E ≤ diskGreen R x x / g ∧ diskGreen R x x / g ≤ Real.log R + E := by
    constructor
    · apply (le_div_iff₀ hg).mpr
      nlinarith [hd.1]
    · apply (div_le_iff₀ hg).mpr
      nlinarith [hd.2]
  have hd0 := hdiag 0 hdiag0
  have hdw := hdiag w hdiagw
  have hlo0 : (2 * Real.log R - Real.log (Real.sqrt (normSq w))) - (2 * E + 1 / g) ≤
      (diskGreen R 0 0 + diskGreen R 0 w - 1) / g := by
    rw [sub_div, add_div]
    dsimp [E, g] at *
    linarith
  have hup0 : (diskGreen R 0 0 + diskGreen R 0 w - 1) / g ≤
      (2 * Real.log R - Real.log (Real.sqrt (normSq w))) + (2 * E + 1 / g) := by
    rw [sub_div, add_div]
    have hi : 0 < 1 / g := by positivity
    dsimp [E, g] at *
    linarith
  have hupw : (diskGreen R 0 w + diskGreen R w w - 1) / g ≤
      (2 * Real.log R - Real.log (Real.sqrt (normSq w))) + (2 * E + 1 / g) := by
    rw [sub_div, add_div]
    have hi : 0 < 1 / g := by positivity
    dsimp [E, g] at *
    linarith
  change |twoSiteDiscreteRowMax (diskFinset R) 0 w / g - _| ≤ 2 * E + 1 / g
  unfold twoSiteDiscreteRowMax
  rw [hsym, ← max_div_div_right hg.le]
  change |max ((diskGreen R 0 0 + diskGreen R 0 w - 1) / g)
    ((diskGreen R 0 w + diskGreen R w w - 1) / g) -
    (2 * Real.log R - Real.log (Real.sqrt (normSq w)))| ≤ 2 * E + 1 / g
  apply abs_le.mpr
  constructor
  · have hh := le_max_left ((diskGreen R 0 0 + diskGreen R 0 w - 1) / g)
      ((diskGreen R 0 w + diskGreen R w w - 1) / g)
    linarith
  · have hh := max_le hup0 hupw
    linarith

end SRWTightness
