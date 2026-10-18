import SRWTightness.ExternalGaussianRegression

open Matrix
open scoped BigOperators
namespace SRWTightness

/-- The reference coefficient reconstructs precisely the subtracted rank-one quadratic form. -/
theorem finite_gaussian_regression_quadratic {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o : ι) (ho : S o o ≠ 0) (u : EuclideanSpace ℝ ι) :
    S o o * (∑ i, u i * (S i o / S o o)) ^ 2 +
      u ⬝ᵥ (finiteGaussianRegressionCov S o) *ᵥ u = u ⬝ᵥ S *ᵥ u := by
  have hrank : S o o * (∑ i, u i * (S i o / S o o)) ^ 2 =
      ∑ i, ∑ j, u i * (S i o * S j o / S o o) * u j := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [ho] <;> ring
  have hres : u ⬝ᵥ (finiteGaussianRegressionCov S o) *ᵥ u =
      u ⬝ᵥ S *ᵥ u - (∑ i, ∑ j, u i * (S i o * S j o / S o o) * u j) := by
    simp only [dotProduct, Matrix.mulVec, finiteGaussianRegressionCov, mul_sub,
      sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [hrank, hres]
  ring

end SRWTightness
