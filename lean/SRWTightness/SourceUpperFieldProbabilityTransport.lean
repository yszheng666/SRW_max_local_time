import SRWTightness.SourceUpperFieldDomination
import SRWTightness.GaussianRegressionMaximaTransport

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- The reconstructed field event is bounded by the enlarged Gaussian plus actual residual law. -/
theorem source_upper_field_probability_transport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S H : Matrix ι ι ℝ) (o : ι) (J : Finset ι) (hJ : J.Nonempty) (σ m C a : ℝ)
    (hv : 0 < H o o) (hC : 0 ≤ C) (hCv : C ≤ H o o)
    (hb : ∀ x ∈ J, |H x o / H o o - 1| ≤ C / H o o) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
      ((gaussianReal 0 (H o o).toNNReal).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ ι)
          (finiteGaussianRegressionCov H o)))).real
      {p | ∃ x ∈ J, a ≤ p.1 x / σ + finiteGaussianRegressionRebuild H o p.2 x} ≤
    ((gaussianReal 0 ((1 + C / H o o) ^ 2 * H o o).toNNReal).prod
      (finiteGaussianMaximumResidualLaw S (finiteGaussianRegressionCov H o) J hJ σ m)).real
        {q | a - m ≤ max q.1 0 + q.2} := by
  have ht := gaussian_regression_maxima_transport S (finiteGaussianRegressionCov H o)
    J hJ σ m (H o o) C
  rw [← ht.map_eq, map_measureReal_apply ht.measurable
    (show MeasurableSet {q : ℝ × ℝ | a - m ≤ max q.1 0 + q.2} from
      measurableSet_le measurable_const (by fun_prop))]
  have he (t : ℝ) : (1 + C / H o o) * max t 0 = max ((1 + C / H o o) * t) 0 := by
    rw [mul_max_of_nonneg _ _ (show 0 ≤ 1 + C / H o o by positivity), mul_zero]
  have hd := source_upper_field_probability_domination
    ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
      ((gaussianReal 0 (H o o).toNNReal).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) (finiteGaussianRegressionCov H o))))
    H o J hJ σ m C a hv hCv hb
  simpa only [Set.preimage_setOf_eq, he] using hd

end SRWTightness
