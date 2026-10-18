import SRWTightness.NormalizedMarks
import SRWTightness.DiskDiagonalLogBound

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Uniform variance control for both interior sites in a common reference disk. -/
theorem pair_mark_variance_log_radius (b : Site) (R : ℝ) (hR : 4 ≤ R)
    (M : Finset Site) (hMD : M ⊆ translateFinset b (diskFinset R)) (y : M)
    (hy : normSq ((y : Site) - b) ≤ (R / 2) ^ 2)
    (α u : ℝ) (hα : 0 < α) (hu : 0 < u)
    (hcap : α * capacity (translateFinset b (diskFinset R)) M ≤ 1)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    |covariance (normalizedMarkSum M k α (2 / Real.pi) u y)
      (normalizedMarkSum M k α (2 / Real.pi) u y)
      (markProductLaw (translateFinset b (diskFinset R)) M α k) -
      (Real.log R - (1 + α) / (2 * (2 / Real.pi)))| ≤
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 2 := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hG : killedGreen (translateFinset b (diskFinset R)) y y =
      diskGreen R ((y : Site) - b) ((y : Site) - b) := by
    have hh := killedGreen_translate b (diskFinset R) ((y : Site) - b) ((y : Site) - b)
    rw [show b + ((y : Site) - b) = (y : Site) by abel] at hh
    exact hh
  have hh := diskGreen_diagonal_interior_log_bound R hR ((y : Site) - b) hy
  have hb := div_le_div_of_nonneg_right hh hg.le
  have he : |diskGreen R ((y : Site) - b) ((y : Site) - b) / (2 / Real.pi) - Real.log R| =
      |diskGreen R ((y : Site) - b) ((y : Site) - b) - (2 / Real.pi) * Real.log R| /
        (2 / Real.pi) := by
    calc
      _ = |(diskGreen R ((y : Site) - b) ((y : Site) - b) -
          (2 / Real.pi) * Real.log R) / (2 / Real.pi)| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_div, abs_of_pos hg]
  rw [← he] at hb
  rw [normalizedMarkSum_covariance _ M hMD α (2 / Real.pi) u hα hg hu hcap k hk y y,
    if_pos rfl, hG]
  convert hb using 1 <;> congr 1 <;> field_simp <;> ring

end SRWTightness
