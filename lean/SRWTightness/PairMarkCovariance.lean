import SRWTightness.PairGreenLogDistance
import SRWTightness.NormalizedMarks
import SRWTightness.GreenTranslation

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual reference-mark cross covariance has the logarithmic two-site form. -/
theorem pair_mark_covariance_log_distance (b : Site) (R : ℝ) (M : Finset Site)
    (hMD : M ⊆ translateFinset b (diskFinset R)) (z y : M) (hz : (z : Site) = b)
    (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hR : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ R)
    (α u : ℝ) (hα : 0 < α) (hu : 0 < u)
    (hcap : α * capacity (translateFinset b (diskFinset R)) M ≤ 1)
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    |covariance (normalizedMarkSum M k α (2 / Real.pi) u z)
      (normalizedMarkSum M k α (2 / Real.pi) u y)
      (markProductLaw (translateFinset b (diskFinset R)) M α k) -
      (Real.log (R / Real.sqrt (normSq ((y : Site) - b))) - α / (2 * (2 / Real.pi)))| ≤
        diskGreenEnergyConstant / (2 / Real.pi) + Real.log 2 := by
  have hne : z ≠ y := by
    intro he
    have hy : (y : Site) = b := by simpa only [he] using hz
    simp only [hy, sub_self, normSq, Real.sqrt_zero] at hρ
    norm_num at hρ
  have hG : killedGreen (translateFinset b (diskFinset R)) z y =
      diskGreen R 0 ((y : Site) - b) := by
    rw [hz]
    have hh := killedGreen_translate b (diskFinset R) 0 ((y : Site) - b)
    rw [add_zero, show b + ((y : Site) - b) = (y : Site) by abel] at hh
    exact hh
  rw [normalizedMarkSum_covariance _ M hMD α (2 / Real.pi) u hα (by positivity)
    hu hcap k hk z y, if_neg hne, zero_div, sub_zero, hG]
  convert diskGreen_pair_log_distance R ((y : Site) - b) hρ hR using 1 <;> congr 1 <;> ring

end SRWTightness
