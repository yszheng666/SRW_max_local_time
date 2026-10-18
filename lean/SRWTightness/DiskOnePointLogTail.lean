import SRWTightness.OnePointExponentialTail
import SRWTightness.DiskDiagonalLogBound
import SRWTightness.DiskGreenLogBound

open MeasureTheory

namespace SRWTightness

noncomputable def diskDiagonalError : ℝ := diskGreenEnergyConstant + (2 / Real.pi) * Real.log 2

theorem diskDiagonalError_pos : 0 < diskDiagonalError := by
  have hb := diskGreenEnergyConstant_pos
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  dsimp [diskDiagonalError]
  positivity

/-- Uniform actual one-point tail retaining the spatial first-hitting prefactor. -/
theorem disk_one_point_log_tail : ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 4 ≤ R →
    0 < (2 / Real.pi) * Real.log R - diskDiagonalError → ∀ (x : Site),
    normSq x ≤ (R / 2) ^ 2 → ∀ k : ℕ, 1 ≤ k →
    pathLaw.real {ω | k ≤ localTime ω (exitSteps R ω) x} ≤
      (C * (1 + Real.log (R / max (Real.sqrt (normSq x)) 1)) /
        ((2 / Real.pi) * Real.log R - diskDiagonalError)) *
      Real.exp (-((k - 1 : ℕ) : ℝ) / ((2 / Real.pi) * Real.log R + diskDiagonalError)) := by
  obtain ⟨C, hC, hc⟩ := diskGreen_source_upper
  refine ⟨C, hC, ?_⟩
  intro R hR hd x hx k hk
  have hxin : x ∈ disk R := by change normSq x < R ^ 2; nlinarith
  have hdiag := abs_le.mp (diskGreen_diagonal_interior_log_bound R hR x hx)
  have hlo : (2 / Real.pi) * Real.log R - diskDiagonalError ≤ diskGreen R x x := by
    dsimp [diskDiagonalError]
    linarith [hdiag.1]
  have hhi : diskGreen R x x ≤ (2 / Real.pi) * Real.log R + diskDiagonalError := by
    dsimp [diskDiagonalError]
    linarith [hdiag.2]
  simpa only [domainLocalTime_disk, diskGreen] using occupation_tail_exp_prefactor_upper
    (diskFinset R) 0 x ((mem_diskFinset R x).mpr hxin) k hk _ _ _ hd hlo hhi
      (hc R (by linarith) x hxin)

end SRWTightness
