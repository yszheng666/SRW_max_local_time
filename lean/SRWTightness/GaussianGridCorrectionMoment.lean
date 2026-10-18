import SRWTightness.GaussianGridInverseWeightedMoment
import SRWTightness.BrownianCovarianceCorrection
import SRWTightness.GaussianEventLower

open MeasureTheory Matrix

namespace SRWTightness

/-- The actual grid increment estimates bound the Gaussian covariance correction moment. -/
theorem gaussianGrid_correction_moment (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < (n + 1) + 1, 1 ≤ T (j + 1) - T j)
    (μ : Measure ((Fin ((n + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)))
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hm : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ T (n + 1) →
      Integrable (fun p ↦ (gaussianGridPath T (n + 1) p s -
        gaussianGridPath T (n + 1) p r) ^ 2) μ ∧
      (∫ p, (gaussianGridPath T (n + 1) p s -
        gaussianGridPath T (n + 1) p r) ^ 2 ∂μ) ≤ C * (s - r))
    (hfinal : Integrable (fun p ↦ gaussianGridFinalIncrement T (n + 1) p ^ 2) μ ∧
      (∫ p, gaussianGridFinalIncrement T (n + 1) p ^ 2 ∂μ) ≤ B)
    (e : Fin ((n + 1) + 1) → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ 1 / 8) :
    let K := brownianTimeMatrix T ((n + 1) + 1)
    Integrable (fun p ↦ gaussianInverseCorrection K (K - Matrix.diagonal e) p.1) μ ∧
      (∫ p, gaussianInverseCorrection K (K - Matrix.diagonal e) p.1 ∂μ) ≤
        (8 * max C B) * ∑ i, e i := by
  let K := brownianTimeMatrix T ((n + 1) + 1)
  have hw := gaussianGrid_inverse_weighted_moment T n hT hgap μ C B hC hB hm hfinal e he
  have hq (p : (Fin ((n + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :
      0 ≤ gaussianInverseCorrection K (K - Matrix.diagonal e) p.1 ∧
      gaussianInverseCorrection K (K - Matrix.diagonal e) p.1 ≤
        2 * ∑ i, e i * (K⁻¹ *ᵥ p.1) i ^ 2 :=
    brownianTimeMatrix_inverse_correction T hT _ 1 (by norm_num) hgap e he hesmall p.1
  have hmeas : Measurable (fun p : (Fin ((n + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦
      gaussianInverseCorrection K (K - Matrix.diagonal e) p.1) := (gaussianInverseCorrection_measurable K (K - Matrix.diagonal e)).comp measurable_fst
  have hi := (hw.1.const_mul 2).mono_nonneg hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p ↦ (hq p).1))
    (Filter.Eventually.of_forall (fun p ↦ (hq p).2))
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi (hw.1.const_mul 2) (fun p ↦ (hq p).2)
  rw [integral_const_mul] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hw.2 (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    (by ring))

end SRWTightness
