import SRWTightness.GaussianMeanLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- A uniform Gaussian density bound controls every translated unit rectangle. -/
theorem gaussian_unit_rectangle_bound (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : R.PosDef) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, (gaussianCovarianceDensity R x).toReal ≤ C) (a : Fin 2 → ℝ) :
    (gaussianCoordinateLaw R).real (Set.pi Set.univ (fun j ↦ Set.Ico (a j) (a j + 1)))
      ≤ C := by
  have hfinite (x : Fin 2 → ℝ) : gaussianCovarianceDensity R x ≠ ⊤ := by
    unfold gaussianCovarianceDensity
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.prod_ne_top (fun _ _ ↦ gaussianPDF_ne_top))
  have hmeasure : gaussianCoordinateLaw R ≤ ENNReal.ofReal C • volume := by
    unfold gaussianCoordinateLaw
    rw [multivariateGaussian_coordinate_density R hR, ← withDensity_const]
    exact withDensity_mono (Filter.Eventually.of_forall (fun x ↦
      (ENNReal.le_ofReal_iff_toReal_le (hfinite x) hC).mpr (hbound x)))
  have hh := hmeasure (Set.pi Set.univ (fun j ↦ Set.Ico (a j) (a j + 1)))
  have hvol : volume (Set.pi Set.univ (fun j ↦ Set.Ico (a j) (a j + 1))) = 1 := by
    simp [Real.volume_pi_Ico]
  rw [Measure.smul_apply, smul_eq_mul, hvol, mul_one] at hh
  have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [Measure.real, ENNReal.toReal_ofReal hC] using hh'

end SRWTightness
