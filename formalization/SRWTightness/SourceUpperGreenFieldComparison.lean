import SRWTightness.NormalizedHarmonicReconstruction
import SRWTightness.SourceUpperFieldProbabilityTransport

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- The actual normalized Green-field upper event is bounded by the independent scalar event. -/
theorem source_upper_green_field_comparison (hReg : FiniteGaussianRegressionInput)
    (D E : Finset Site) (hED : E ⊆ D) (o : E) (J : Finset E) (hJ : J.Nonempty)
    (σ m C a : ℝ) (hv : 0 < normalizedHarmonicCov D E σ o o)
    (hC : 0 ≤ C) (hCv : C ≤ normalizedHarmonicCov D E σ o o)
    (hb : ∀ x ∈ J, |normalizedHarmonicCov D E σ x o /
      normalizedHarmonicCov D E σ o o - 1| ≤ C / normalizedHarmonicCov D E σ o o) :
    (gaussianGreenLaw D E).real {φ | ∃ x ∈ J, a ≤ φ x / σ} ≤
      ((gaussianReal 0 ((1 + C / normalizedHarmonicCov D E σ o o) ^ 2 *
        normalizedHarmonicCov D E σ o o).toNNReal).prod
        (finiteGaussianMaximumResidualLaw (greenMatrix E)
          (finiteGaussianRegressionCov (normalizedHarmonicCov D E σ) o) J hJ σ m)).real
            {q | a - m ≤ max q.1 0 + q.2} := by
  have hSet : MeasurableSet {φ : EuclideanSpace ℝ E | ∃ x ∈ J, a ≤ φ x} := by
    rw [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro x
    by_cases hx : x ∈ J
    · simp only [hx, true_and]
      exact measurableSet_le measurable_const (by fun_prop)
    · simp [hx]
  have hNorm : (gaussianGreenLaw D E).real {φ | ∃ x ∈ J, a ≤ φ x / σ} =
      ((gaussianGreenLaw D E).map (fun φ ↦ σ⁻¹ • φ)).real
        {φ | ∃ x ∈ J, a ≤ φ x} := by
    rw [map_measureReal_apply (by fun_prop) hSet]
    congr 1
    ext φ
    simp [div_eq_mul_inv, mul_comm]
  rw [hNorm, ← normalized_harmonic_regression_reconstruction hReg D E hED o σ hv,
    map_measureReal_apply
      (by unfold finiteGaussianRegressionRebuild; fun_prop) hSet]
  have ht := source_upper_field_probability_transport (greenMatrix E)
    (normalizedHarmonicCov D E σ) o J hJ σ m C a hv hC hCv hb
  have hG : gaussianGreenLaw E E =
      multivariateGaussian (0 : EuclideanSpace ℝ E) (greenMatrix E) := rfl
  rw [hG]
  simpa [div_eq_mul_inv, mul_comm] using ht

end SRWTightness
