import SRWTightness.ProjectedMarkGaussianBranches
import SRWTightness.GaussianMarkThresholdNormalization

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual mark comparison with the positive threshold in manuscript normalization. -/
theorem projected_fixed_mark_normalized_branches (D A K : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (α g : ℝ) (hα : 0 ≤ α) (hg : 0 < g)
    (hcap : α * capacity D K ≤ 1) (k a : ℕ) (hk : 1 ≤ k) (ha : 1 ≤ a) :
    (markProductLaw D K α k).real
      {Y | ∃ z : A, a ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
      576 * ((gaussianGreenLaw D A).real
        {φ | ∃ z : A, Real.sqrt (2 * (a : ℝ) / g) -
          Real.sqrt (α / g) * Real.sqrt (2 * (k : ℝ)) ≤ φ z / Real.sqrt g} +
        ∑ z : A, Real.exp
          (-(Real.sqrt (2 * (a : ℝ)) + Real.sqrt (2 * ((k : ℝ) * α))) ^ 2 /
            (2 * killedGreen D z z))) := by
  have hb := projected_fixed_mark_gaussian_branches D A K hAK hKD α hα hcap k a hk ha
  rw [gaussian_mark_threshold_event A k a α g hα hg] at hb
  exact hb

end SRWTightness
