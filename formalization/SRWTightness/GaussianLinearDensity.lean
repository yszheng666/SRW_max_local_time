import SRWTightness.LinearDensityTransport
import SRWTightness.GaussianProductDensity

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace SRWTightness

/-- The density of an invertible linear image of independent standard Gaussians. -/
theorem gaussianPi_matrix_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : IsUnit M) :
    (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)).map (fun x ↦ M *ᵥ x) =
      volume.withDensity (fun y ↦ ENNReal.ofReal (abs M.det⁻¹) *
        ∏ i, gaussianPDF 0 1 ((M⁻¹ *ᵥ y) i)) := by
  rw [standardGaussianPi_withDensity]
  apply matrix_map_withDensity M hM
  apply Finset.measurable_prod
  intro i _
  exact (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)

theorem gaussianPi_density_toReal {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (∏ i, gaussianPDF 0 1 (x i)).toReal =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι * Real.exp (-(∑ i, x i ^ 2) / 2) := by
  simp only [ENNReal.toReal_prod, toReal_gaussianPDF, gaussianPDFReal, NNReal.coe_one,
    sub_zero, mul_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Real.exp_sum, ← Finset.sum_div, Finset.sum_neg_distrib]

theorem gaussianPi_matrix_density_toReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (y : ι → ℝ) :
    (ENNReal.ofReal (abs M.det⁻¹) * ∏ i, gaussianPDF 0 1 ((M⁻¹ *ᵥ y) i)).toReal =
      abs M.det⁻¹ * ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι) *
        Real.exp (-(∑ i, (M⁻¹ *ᵥ y) i ^ 2) / 2) := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), gaussianPi_density_toReal]
  exact (mul_assoc _ _ _).symm

end SRWTightness
