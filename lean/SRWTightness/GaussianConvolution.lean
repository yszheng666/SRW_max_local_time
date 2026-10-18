import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

namespace SRWTightness

/-- Independent centered Gaussian vectors add their actual covariance matrices. -/
theorem multivariateGaussian_zero_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Matrix ι ι ℝ) (hS : S.PosSemidef) (hT : T.PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) T)).map (fun p ↦ p.1 + p.2) =
        multivariateGaussian (0 : EuclideanSpace ℝ ι) (S + T) := by
  apply Measure.ext_of_charFun
  rw [charFun_map_add_prod_eq_mul]
  funext x
  simp only [Pi.mul_apply, charFun_multivariateGaussian hS,
    charFun_multivariateGaussian hT, charFun_multivariateGaussian (hS.add hT),
    inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [← Complex.exp_add]
  congr 1
  simp only [Matrix.add_mulVec, dotProduct_add, Complex.ofReal_add]
  ring

end SRWTightness
