import SRWTightness.LaplaceResolvent
import SRWTightness.PoissonGenerating

open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

 theorem laplace_inverse_vector (D A : Finset Site) (hAD : A ⊆ D)
    (f : A → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (observationResolventMatrix D A (fun z ↦ (1 + f z)⁻¹))⁻¹.mulVec 1 =
      fun z ↦ (1 + f z) * ((laplaceGreenMatrix D A f)⁻¹.mulVec 1) z := by
  let B := observationResolventMatrix D A (fun z ↦ (1 + f z)⁻¹)
  let L := Matrix.diagonal (fun z ↦ 1 + f z)
  let C := laplaceGreenMatrix D A f
  have hB : IsUnit B := observationResolventMatrix_isUnit D A hAD _
    (fun z ↦ inv_nonneg.mpr (by linarith [hf z]))
    (fun z ↦ inv_le_one_of_one_le₀ (by linarith [hf z]))
  have hC : IsUnit C := laplaceGreenMatrix_isUnit D A hAD f hf
  have hBL : B * L = C := laplace_resolvent_factor D A f hf
  have he : B * (L * C⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, hBL, Matrix.mul_nonsing_inv C
      ((Matrix.isUnit_iff_isUnit_det C).mp hC)]
  have hinv : B⁻¹ = L * C⁻¹ := Matrix.inv_eq_right_inv he
  change B⁻¹.mulVec 1 = _
  rw [hinv, ← Matrix.mulVec_mulVec]
  funext z
  exact Matrix.mulVec_diagonal _ _ _

/-- The discrete Poissonized generating function after the exponential-holding substitution.
Construction of the actual holding-time random variables is a separate step. -/
theorem poissonized_marks_laplace_substitution (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (r : ℝ≥0)
    (f : A → ℝ) (hf : ∀ z, 0 ≤ f z) :
    (∫ k : ℕ, (∫ Y, markMonomial (fun z ↦ (1 + f z)⁻¹) (sumMarks A k Y)
      ∂markProductLaw D A α k) ∂poissonMeasure r) =
      Real.exp (-(r : ℝ) * α *
        ∑ z : A, f z * ((laplaceGreenMatrix D A f)⁻¹.mulVec 1) z) := by
  rw [poissonized_marks_generating D A hAD α hα hcap r _
    (fun z ↦ inv_nonneg.mpr (by linarith [hf z]))
    (fun z ↦ inv_le_one_of_one_le₀ (by linarith [hf z])), laplace_inverse_vector D A hAD f hf]
  have ht (z : A) : ((1 + f z)⁻¹ - 1) *
      ((1 + f z) * ((laplaceGreenMatrix D A f)⁻¹.mulVec 1) z) =
      -(f z * ((laplaceGreenMatrix D A f)⁻¹.mulVec 1) z) := by
    have hn : 1 + f z ≠ 0 := by linarith [hf z]
    field_simp
    ring
  simp_rw [ht, Finset.sum_neg_distrib]
  congr 1
  ring

end SRWTightness
