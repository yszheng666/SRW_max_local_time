import SRWTightness.HarmonicRegressionBounds

open Matrix
namespace SRWTightness

/-- A positive semidefinite real covariance has nonnegative coordinate-increment variance. -/
theorem covariance_increment_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (x y : ι) :
    0 ≤ S x x + S y y - 2 * S x y := by
  have hq := hS.dotProduct_mulVec_nonneg (Pi.single x 1 - Pi.single y 1)
  have hsym : S y x = S x y := by simpa using hS.isHermitian.apply x y
  simp [mulVec_sub, sub_dotProduct, single_dotProduct, mulVec_single] at hq
  nlinarith only [hq, hsym]

/-- Covariance positivity supplies the lower increment condition in the regression bound. -/
theorem covariance_regression_coefficient_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (o x : ι) (C : ℝ)
    (hv : 0 < S o o) (hdiag : |S x x - S o o| ≤ C)
    (hinc : S x x + S o o - 2 * S x o ≤ C) :
    |S x o / S o o - 1| ≤ C / S o o :=
  finite_gaussian_regression_coefficient_bound S o x C hv hdiag
    (covariance_increment_nonneg S hS x o) hinc

end SRWTightness
