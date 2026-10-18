import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Algebra.BigOperators.Pi

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Finite real Gaussian vectors are determined by coordinate means and covariances. -/
theorem gaussian_finite_law_eq_of_mean_covariance {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω → ι → ℝ)
    (hX : HasGaussianLaw X μ) (hY : HasGaussianLaw Y μ)
    (hm : ∀ i, (∫ ω, X ω i ∂μ) = ∫ ω, Y ω i ∂μ)
    (hc : ∀ i j, cov[fun ω ↦ X ω i, fun ω ↦ X ω j; μ] =
      cov[fun ω ↦ Y ω i, fun ω ↦ Y ω j; μ]) : μ.map X = μ.map Y := by
  have hx (i : ι) : MemLp (fun ω ↦ X ω i) 2 μ :=
    (hX.map (ContinuousLinearMap.proj i)).memLp_two
  have hy (i : ι) : MemLp (fun ω ↦ Y ω i) 2 μ :=
    (hY.map (ContinuousLinearMap.proj i)).memLp_two
  apply Measure.ext_of_charFunDual
  funext L
  rw [hX.charFunDual_map_eq L, hY.charFunDual_map_eq L]
  let a := fun i ↦ L (Pi.single i 1)
  have he (Z : Ω → ι → ℝ) : L ∘ Z = fun ω ↦ ∑ i, a i * Z ω i := by
    funext ω
    change L (Z ω) = _
    conv_lhs => rw [pi_eq_sum_univ' (Z ω)]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  rw [he X, he Y]
  have hmean : (∫ ω, ∑ i, a i * X ω i ∂μ) = ∫ ω, ∑ i, a i * Y ω i ∂μ := by
    rw [integral_finsetSum _ (fun i _ ↦ (hx i).integrable (by norm_num) |>.const_mul _),
      integral_finsetSum _ (fun i _ ↦ (hy i).integrable (by norm_num) |>.const_mul _)]
    simp_rw [integral_const_mul, hm]
  have hvar : Var[fun ω ↦ ∑ i, a i * X ω i; μ] =
      Var[fun ω ↦ ∑ i, a i * Y ω i; μ] := by
    rw [← covariance_self
      (memLp_finsetSum Finset.univ (fun i _ ↦ (hx i).const_mul (a i))).aemeasurable,
      ← covariance_self
        (memLp_finsetSum Finset.univ (fun i _ ↦ (hy i).const_mul (a i))).aemeasurable]
    rw [covariance_fun_sum_fun_sum (fun i ↦ (hx i).const_mul _) (fun i ↦ (hx i).const_mul _),
      covariance_fun_sum_fun_sum (fun i ↦ (hy i).const_mul _) (fun i ↦ (hy i).const_mul _)]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right, hc]
  rw [hmean, hvar]

end SRWTightness
