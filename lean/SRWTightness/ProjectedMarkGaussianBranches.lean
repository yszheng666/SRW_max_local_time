import SRWTightness.GaussianShiftedBranches

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Actual projected fixed-count marks split into a terminal upper event and a Gaussian error. -/
theorem projected_fixed_mark_gaussian_branches (D A K : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (k a : ℕ) (hk : 1 ≤ k) (ha : 1 ≤ a) :
    (markProductLaw D K α k).real
      {Y | ∃ z : A, a ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
      576 * ((gaussianGreenLaw D A).real
        {φ | ∃ z : A, Real.sqrt (2 * (a : ℝ)) - Real.sqrt (2 * ((k : ℝ) * α)) ≤ φ z} +
        ∑ z : A, Real.exp
          (-(Real.sqrt (2 * (a : ℝ)) + Real.sqrt (2 * ((k : ℝ) * α))) ^ 2 /
            (2 * killedGreen D z z))) := by
  exact (projected_fixed_mark_exceedance_le_gaussian D A K hAK hKD α hα hcap k a hk ha).trans
    (mul_le_mul_of_nonneg_left
      (shiftedGaussianExceedance_branch_bound D A (hAK.trans hKD) ((k : ℝ) * α) a)
      (by norm_num))

end SRWTightness
