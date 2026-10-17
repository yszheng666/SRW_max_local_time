import SRWTightness.GaussianOccupationComparison
import SRWTightness.GaussianTail

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The lower Gaussian branch has the same one-coordinate subGaussian envelope. -/
theorem gaussianGreenLaw_negative_coordinate_tail (D A : Finset Site) (hAD : A ⊆ D)
    (z : A) (s : ℝ) (hs : 0 ≤ s) :
    (gaussianGreenLaw D A).real {φ | s ≤ -φ z} ≤
      Real.exp (-s ^ 2 / (2 * killedGreen D z z)) := by
  have he := (gaussianGreenLaw_subgaussian D A hAD z).neg.measure_ge_le hs
  simpa only [Pi.neg_apply, Real.coe_toNNReal _ (killedGreen_nonneg D z z)] using he

/-- A union bound controls the negative branch over the actual observations. -/
theorem gaussianGreenLaw_negative_max_tail (D A : Finset Site) (hAD : A ⊆ D)
    (s : ℝ) (hs : 0 ≤ s) :
    (gaussianGreenLaw D A).real {φ | ∃ z : A, s ≤ -φ z} ≤
      ∑ z : A, Real.exp (-s ^ 2 / (2 * killedGreen D z z)) := by
  have he : {φ : EuclideanSpace ℝ A | ∃ z : A, s ≤ -φ z} =
      ⋃ z : A, {φ : EuclideanSpace ℝ A | s ≤ -φ z} := by ext φ; simp
  rw [he]
  exact (measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum (fun z _ ↦ gaussianGreenLaw_negative_coordinate_tail D A hAD z s hs))

/-- Separate the positive terminal maximum from the strongly suppressed negative branch. -/
theorem shiftedGaussianExceedance_branch_bound (D A : Finset Site) (hAD : A ⊆ D)
    (u : ℝ) (a : ℕ) :
    (gaussianGreenLaw D A).real (shiftedGaussianExceedance A u a) ≤
      (gaussianGreenLaw D A).real
        {φ | ∃ z : A, Real.sqrt (2 * (a : ℝ)) - Real.sqrt (2 * u) ≤ φ z} +
      ∑ z : A, Real.exp (-(Real.sqrt (2 * (a : ℝ)) + Real.sqrt (2 * u)) ^ 2 /
        (2 * killedGreen D z z)) := by
  have hsub : shiftedGaussianExceedance A u a ⊆
      {φ | ∃ z : A, Real.sqrt (2 * (a : ℝ)) - Real.sqrt (2 * u) ≤ φ z} ∪
      {φ | ∃ z : A, Real.sqrt (2 * (a : ℝ)) + Real.sqrt (2 * u) ≤ -φ z} := by
    rintro φ ⟨z, hz⟩
    by_cases hsign : 0 ≤ φ z + Real.sqrt (2 * u)
    · rw [abs_of_nonneg hsign] at hz
      exact Or.inl ⟨z, by linarith⟩
    · rw [abs_of_nonpos (le_of_not_ge hsign)] at hz
      exact Or.inr ⟨z, by linarith⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add le_rfl (gaussianGreenLaw_negative_max_tail D A hAD
        (Real.sqrt (2 * (a : ℝ)) + Real.sqrt (2 * u)) (by positivity))))

end SRWTightness
