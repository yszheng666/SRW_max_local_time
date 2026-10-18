import SRWTightness.GaussianProductDensity
import SRWTightness.GaussianResolventShift
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

noncomputable def gaussianQuadraticLaplace {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (f c : ι → ℝ) : ℝ :=
  ∫ x : ι → ℝ, Real.exp (-(∑ i, f i * (B.mulVec x i + c i) ^ 2) / 2)
    ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)

 theorem gaussianQuadraticLaplace_energy {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (f c : ι → ℝ) :
    gaussianQuadraticLaplace B f c =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
        ∫ x : ι → ℝ, Real.exp (-gaussianEnergy B f c x / 2) := by
  rw [gaussianQuadraticLaplace, standardGaussianPi_integral]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [← Real.exp_add]
  congr 1
  unfold gaussianEnergy
  ring

/-- The exact shifted/unshifted quadratic Laplace relation from completion of the square.
No unspecified Gaussian integration or determinant identity is used. -/
theorem gaussianQuadraticLaplace_shift_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.transpose = B) (f c : ι → ℝ)
    (hC : IsUnit (quadraticResolvent B f)) :
    gaussianQuadraticLaplace B f c = gaussianQuadraticLaplace B f 0 *
      Real.exp (-(∑ i, f i * c i * ((quadraticResolvent B f)⁻¹.mulVec c) i) / 2) := by
  rw [gaussianQuadraticLaplace_energy, gaussianQuadraticLaplace_energy]
  have he (x : ι → ℝ) : Real.exp (-gaussianEnergy B f c x / 2) =
      Real.exp (-gaussianEnergy B f 0 (x + gaussianShiftVector B f c) / 2) *
        Real.exp (-(∑ i, f i * c i * ((quadraticResolvent B f)⁻¹.mulVec c) i) / 2) := by
    rw [gaussianEnergy_resolvent_complete B hB f c x hC, neg_add, add_div, Real.exp_add]
  simp_rw [he]
  rw [integral_mul_const, integral_add_right_eq_self
    (fun x : ι → ℝ ↦ Real.exp (-gaussianEnergy B f 0 x / 2)) (gaussianShiftVector B f c)]
  ring

end SRWTightness
