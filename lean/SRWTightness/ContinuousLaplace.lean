import SRWTightness.OccupationLaplaceSupport

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

/-- Manuscript (3.6) for the actual Poissonized continuous occupation probability law. -/
theorem continuousOccupation_laplace (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (r : ℝ≥0)
    (f : A → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (∫ L, Real.exp (-(∑ z : A, f z * L z)) ∂continuousOccupationLaw D A α r) =
      Real.exp (-(r : ℝ) * α *
        ∑ z : A, f z * ((laplaceGreenMatrix D A f)⁻¹.mulVec 1) z) := by
  letI := markCountKernel_isMarkov D A α hα hcap
  letI := continuousOccupationLaw_isProbabilityMeasure D A α hα hcap r
  let v : A → ℝ := fun z ↦ (1 + f z)⁻¹
  have hv0 (z : A) : 0 ≤ v z := inv_nonneg.mpr (by linarith [hf z])
  have hv1 (z : A) : v z ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hf z])
  have hI := integrable_occupationLaplace (continuousOccupationLaw D A α r)
    (continuousOccupationLaw_nonneg D A α r) f hf
  change (∫ L, occupationLaplace f L ∂continuousOccupationLaw D A α r) = _
  rw [continuousOccupationLaw, integral_kernel_comp_real _ _ _ hI]
  have hh (Y : Mark A) : (∫ L, occupationLaplace f L ∂holdingKernel A Y) = markMonomial v Y :=
    holdingKernel_laplace A Y f hf
  simp_rw [hh]
  have hm := integrable_bounded_mark_test A (markCountKernel D A α ∘ₘ poissonMeasure r)
    (markMonomial v) (measurable_markMonomial v) 1 (norm_markMonomial_le_one v hv0 hv1)
  rw [integral_kernel_comp_real _ _ _ hm]
  have hk (k : ℕ) : (∫ Y, markMonomial v Y ∂markCountKernel D A α k) =
      ∫ Y, markMonomial v (sumMarks A k Y) ∂markProductLaw D A α k :=
    integral_map (measurable_sumMarks A k).aemeasurable (measurable_markMonomial v).aestronglyMeasurable
  simp_rw [hk]
  exact poissonized_marks_laplace_substitution D A hAD α hα hcap r f hf

end SRWTightness
