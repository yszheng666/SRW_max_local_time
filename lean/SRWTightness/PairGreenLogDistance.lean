import SRWTightness.DiskGreenEnergyBounds
import SRWTightness.LatticeTranslation

namespace SRWTightness

/-- A center-to-interior Green entry tracks logarithmic separation with a uniform error. -/
theorem diskGreen_pair_log_distance (R : ℝ) (y : Site)
    (hρ : 1 ≤ Real.sqrt (normSq y)) (hR : 4 * Real.sqrt (normSq y) ≤ R) :
    |diskGreen R 0 y / (2 / Real.pi) -
      Real.log (R / Real.sqrt (normSq y))| ≤
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 2 := by
  let ρ := Real.sqrt (normSq y)
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith
  have hR0 : 0 < R := by dsimp [ρ] at hρ0; linarith
  have hs := Real.sq_sqrt (normSq_nonneg y)
  have hy : y ∈ disk (2 * ρ) := by
    change normSq y < (2 * ρ) ^ 2
    dsimp [ρ] at *
    nlinarith
  have hlo := diskGreen_inner_lower R (2 * ρ) (by dsimp [ρ]; linarith)
    (by dsimp [ρ]; linarith) y hy
  have hhi := diskGreen_inner_radius_upper R (2 * ρ) (by dsimp [ρ]; linarith)
    (by dsimp [ρ]; linarith) y hy (by simpa [ρ] using le_max_left (Real.sqrt (normSq y)) 1)
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hl : Real.log (R / (2 * ρ)) = Real.log (R / ρ) - Real.log 2 := by
    rw [Real.log_div hR0.ne' (mul_pos (by norm_num) hρ0).ne',
      Real.log_mul (by norm_num) hρ0.ne', Real.log_div hR0.ne' hρ0.ne']
    ring
  rw [hl] at hlo hhi
  have he : diskGreenEnergyConstant / (2 / Real.pi) * (2 / Real.pi) =
      diskGreenEnergyConstant := div_mul_cancel₀ _ hg.ne'
  have lo : Real.log (R / ρ) - Real.log 2 - diskGreenEnergyConstant / (2 / Real.pi) ≤
      diskGreen R 0 y / (2 / Real.pi) := (le_div_iff₀ hg).mpr (by nlinarith)
  have hi : diskGreen R 0 y / (2 / Real.pi) ≤
      Real.log (R / ρ) - Real.log 2 + diskGreenEnergyConstant / (2 / Real.pi) :=
    (div_le_iff₀ hg).mpr (by nlinarith)
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  apply abs_le.mpr
  constructor <;> nlinarith

end SRWTightness
