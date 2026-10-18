import SRWTightness.SourceUpperSmallHeightTail
import SRWTightness.FiniteGaussianPositiveMaximumLaw

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- A field maximum tail starting at height one controls its centered positive maximum law. -/
theorem source_upper_fine_positive_maximum_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) (σ m D c h : ℝ)
    (hD : 0 ≤ D) (hc : 0 ≤ c) (hh : 1 ≤ h)
    (hTail : ∀ u : ℝ, 1 ≤ u →
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
        {φ | ∃ x ∈ J, m + u ≤ φ x / σ} ≤
          D * (1 + u) * Real.exp (-2 * u - c * u ^ 2 / h)) :
    ∀ u : ℝ, 0 ≤ u → (finiteGaussianPositiveMaximumLaw S J hJ σ m).real (Ici u) ≤
      (D + Real.exp (2 + c)) * (1 + u) * Real.exp (-2 * u - c * u ^ 2 / h) := by
  letI := finiteGaussianPositiveMaximumLaw_isProbabilityMeasure S J hJ σ m
  apply source_upper_small_height_tail _ D c h hD hc hh
  intro u hu
  rw [finiteGaussianPositiveMaximumLaw_tail S J hJ σ m u (by linarith)]
  exact hTail u hu

/-- The actual positive fine maximum plus absolute residual maximum has the combined tail. -/
theorem source_upper_actual_maxima_sum_tail (hConv : PositiveConvolutionInput)
    (hMoment : SubGaussianPositiveMomentInput) (A b D c : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hD : 0 ≤ D) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (S T : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) (σ m h : ℝ),
      1 ≤ h → c / h ≤ b / 2 →
      (∀ u : ℝ, 1 ≤ u →
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
          {φ | ∃ x ∈ J, m + u ≤ φ x / σ} ≤
            D * (1 + u) * Real.exp (-2 * u - c * u ^ 2 / h)) →
      (∀ u : ℝ, 0 ≤ u →
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) T).real
          {φ | ∃ x ∈ J, u ≤ |φ x|} ≤ A * Real.exp (-b * u ^ 2)) →
      ∀ z : ℝ, 0 ≤ z →
        ((finiteGaussianPositiveMaximumLaw S J hJ σ m).prod
          (finiteGaussianAbsMaximumLaw T J hJ)).real {p | z ≤ p.1 + p.2} ≤
            C * (1 + z) * Real.exp (-2 * z - c * z ^ 2 / (2 * h)) := by
  obtain ⟨C, hC, hbound⟩ := source_upper_combined_tail_probability hConv hMoment
    A b (D + Real.exp (2 + c)) hA hb (by positivity)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ S T J hJ σ m h hh hch hFine hRes z hz
  letI := finiteGaussianPositiveMaximumLaw_isProbabilityMeasure S J hJ σ m
  letI := finiteGaussianAbsMaximumLaw_isProbabilityMeasure T J hJ
  apply hbound _ _ (finiteGaussianAbsMaximumLaw_nonneg T J hJ) _ h c
    (by linarith) hc hch
    (source_upper_fine_positive_maximum_tail S J hJ σ m D c h hD hc hh hFine) z hz
  intro u hu
  rw [finiteGaussianAbsMaximumLaw_tail]
  exact hRes u hu

end SRWTightness
