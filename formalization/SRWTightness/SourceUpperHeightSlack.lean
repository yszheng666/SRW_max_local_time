import SRWTightness.SourceUpperBarrierHeightBound

namespace SRWTightness

/-- A fourth-root terminal barrier leaves room below the square-root admissibility cutoff. -/
theorem terminal_fourth_root_slack (d L : ℝ) (hd : 16 ≤ d)
    (hL : L + 5 ≤ Real.sqrt d / 2) :
    d ^ (1 / 4 : ℝ) + L + 5 ≤ Real.sqrt d := by
  have hd0 : 0 ≤ d := by linarith
  have hw : (d ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt d := by
    rw [← Real.rpow_two, ← Real.rpow_mul hd0, Real.sqrt_eq_rpow]
    norm_num
  have hv : 4 ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by nlinarith)
  have hh : d ^ (1 / 4 : ℝ) ≤ Real.sqrt d / 2 := by
    nlinarith [sq_nonneg (d ^ (1 / 4 : ℝ) - 2)]
  linarith

/-- A unit threshold perturbation is allowed throughout the terminal barrier range. -/
theorem terminal_perturbed_height_admissible (d L q ε : ℝ) (hd : 16 ≤ d)
    (hL : L + 5 ≤ Real.sqrt d / 2)
    (hq : -4 - L - d ^ (1 / 4 : ℝ) ≤ q) (hε : -1 ≤ ε) :
    -Real.sqrt d ≤ q + ε := by
  have hh := terminal_fourth_root_slack d L hd hL
  linarith

end SRWTightness
