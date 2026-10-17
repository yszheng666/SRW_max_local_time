import SRWTightness.IndependentMarks

open MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def normalizedMarkSum (K : Finset Site) (k : ℕ) (α g u : ℝ)
    (z : K) (Y : MarkSamples K k) : ℝ :=
  ((∑ i : Fin k, (Y i z : ℝ)) - α * k) / (u * Real.sqrt (α * g))

 theorem normalized_covariance_algebra (α g u G δ : ℝ) (hα : 0 < α)
    (hg : 0 < g) (hu : 0 < u) :
    ((u ^ 2 / 2) * (2 * α * G - α * δ - α ^ 2)) /
      (u * Real.sqrt (α * g)) / (u * Real.sqrt (α * g)) =
      G / g - δ / (2 * g) - α / (2 * g) := by
  have hs : (Real.sqrt (α * g)) ^ 2 = α * g := Real.sq_sqrt (mul_pos hα hg).le
  have hsne : Real.sqrt (α * g) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (mul_pos hα hg))
  calc
    _ = ((u ^ 2 / 2) * (2 * α * G - α * δ - α ^ 2)) /
        (u ^ 2 * (Real.sqrt (α * g)) ^ 2) := by ring
    _ = _ := by
      rw [hs]
      field_simp

/-- Manuscript (2.19), for an actual finite product of independent reference marks. -/
theorem normalizedMarkSum_covariance (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) (y z : K) :
    covariance (normalizedMarkSum K k α g u y) (normalizedMarkSum K k α g u z)
      (markProductLaw D K α k) =
      killedGreen D y z / g - (if y = z then 1 else 0) / (2 * g) - α / (2 * g) := by
  letI := markProductLaw_isProbabilityMeasure D K α hα.le hcap k
  have hi (w : K) : Integrable (fun Y : MarkSamples K k ↦ ∑ i : Fin k, (Y i w : ℝ))
      (markProductLaw D K α k) := by
    apply integrable_finsetSum
    intro i hi
    exact (mark_coordinate_memLp_two D K α hα.le hcap k i w).integrable (by norm_num)
  unfold normalizedMarkSum
  rw [covariance_fun_div_left, covariance_fun_div_right,
    covariance_sub_const_left (hi y), covariance_sub_const_right (hi z),
    mark_sum_covariance D K hKD α hα.le hcap k y z, ← hk]
  exact normalized_covariance_algebra α g u _ _ hα hg hu

end SRWTightness
