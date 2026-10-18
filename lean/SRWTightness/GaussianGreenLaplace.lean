import SRWTightness.GaussianPiRepresentation
import SRWTightness.GaussianQuadraticRatio
import SRWTightness.LaplaceResolvent

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace SRWTightness

noncomputable def gaussianGreenSquaredLaplace (D A : Finset Site) (f c : A → ℝ) : ℝ :=
  ∫ φ : EuclideanSpace ℝ A, Real.exp (-(∑ z, f z * (φ z + c z) ^ 2) / 2)
    ∂gaussianGreenLaw D A

 theorem gaussianGreenSquaredLaplace_ratio (D A : Finset Site) (hAD : A ⊆ D)
    (f : A → ℝ) (hf : ∀ z, 0 ≤ f z) (c : A → ℝ) :
    gaussianGreenSquaredLaplace D A f c = gaussianGreenSquaredLaplace D A f 0 *
      Real.exp (-(∑ z, f z * c z * ((laplaceGreenMatrix D A f)⁻¹.mulVec c) z) / 2) := by
  have hG := (observationGreen_posDef D A hAD).posSemidef
  have hC : quadraticResolvent (CFC.sqrt (observationGreen D A)) f =
      laplaceGreenMatrix D A f := by
    unfold quadraticResolvent laplaceGreenMatrix
    rw [matrix_sqrt_square _ hG]
  have hU : IsUnit (quadraticResolvent (CFC.sqrt (observationGreen D A)) f) := by
    rw [hC]
    exact laplaceGreenMatrix_isUnit D A hAD f hf
  have he := gaussianQuadraticLaplace_shift_ratio (CFC.sqrt (observationGreen D A))
    (matrix_sqrt_symmetric _) f c hU
  rw [hC] at he
  simpa only [gaussianGreenSquaredLaplace, gaussianGreenLaw,
    integral_multivariateGaussian_quadratic, gaussianQuadraticLaplace] using he

 theorem gaussianGreenSquaredLaplace_constant_shift (D A : Finset Site) (hAD : A ⊆ D)
    (f : A → ℝ) (hf : ∀ z, 0 ≤ f z) (u : ℝ) (hu : 0 ≤ u) :
    gaussianGreenSquaredLaplace D A f (fun _ ↦ Real.sqrt (2 * u)) =
      gaussianGreenSquaredLaplace D A f 0 *
        Real.exp (-u * ∑ z, f z * ((laplaceGreenMatrix D A f)⁻¹.mulVec 1) z) := by
  rw [gaussianGreenSquaredLaplace_ratio D A hAD f hf]
  congr 1
  congr 1
  let s := Real.sqrt (2 * u)
  have hs : s ^ 2 = 2 * u := Real.sq_sqrt (by positivity)
  have hv : (laplaceGreenMatrix D A f)⁻¹.mulVec (fun _ ↦ s) =
      fun z ↦ s * ((laplaceGreenMatrix D A f)⁻¹.mulVec 1) z := by
    funext z
    simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change -(∑ z, f z * s * ((laplaceGreenMatrix D A f)⁻¹.mulVec (fun _ ↦ s)) z) / 2 = _
  rw [hv]
  have he : (∑ z, f z * s * (s * ((laplaceGreenMatrix D A f)⁻¹.mulVec 1) z)) =
      s ^ 2 * ∑ z, f z * ((laplaceGreenMatrix D A f)⁻¹.mulVec 1) z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [he, hs]
  ring

end SRWTightness
