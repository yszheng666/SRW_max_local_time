import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Algebra.BigOperators.Pi

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Finite Gaussian laws on different sample spaces agree when means and covariances agree. -/
theorem gaussian_cross_space_finite_law_eq {Ω Ξ ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ι → ℝ) (Y : Ξ → ι → ℝ)
    (hX : HasGaussianLaw X μ) (hY : HasGaussianLaw Y ν)
    (hm : ∀ i, (∫ ω, X ω i ∂μ) = ∫ ω, Y ω i ∂ν)
    (hc : ∀ i j, cov[fun ω ↦ X ω i, fun ω ↦ X ω j; μ] =
      cov[fun ω ↦ Y ω i, fun ω ↦ Y ω j; ν]) : μ.map X = ν.map Y := by
  have hx (i : ι) : MemLp (fun ω ↦ X ω i) 2 μ :=
    (hX.map (ContinuousLinearMap.proj i)).memLp_two
  have hy (i : ι) : MemLp (fun ω ↦ Y ω i) 2 ν :=
    (hY.map (ContinuousLinearMap.proj i)).memLp_two
  apply Measure.ext_of_charFunDual
  funext L
  rw [hX.charFunDual_map_eq L, hY.charFunDual_map_eq L]
  let a := fun i ↦ L (Pi.single i 1)
  have he (z : ι → ℝ) : L z = ∑ i, a i * z i := by
    conv_lhs => rw [pi_eq_sum_univ' z]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  have heX : L ∘ X = fun ω ↦ ∑ i, a i * X ω i := funext (fun ω ↦ he (X ω))
  have heY : L ∘ Y = fun ω ↦ ∑ i, a i * Y ω i := funext (fun ω ↦ he (Y ω))
  rw [heX, heY]
  have hmean : (∫ ω, ∑ i, a i * X ω i ∂μ) = ∫ ω, ∑ i, a i * Y ω i ∂ν := by
    rw [integral_finsetSum _ (fun i _ ↦ (hx i).integrable (by norm_num) |>.const_mul _),
      integral_finsetSum _ (fun i _ ↦ (hy i).integrable (by norm_num) |>.const_mul _)]
    simp_rw [integral_const_mul, hm]
  have hvar : Var[fun ω ↦ ∑ i, a i * X ω i; μ] =
      Var[fun ω ↦ ∑ i, a i * Y ω i; ν] := by
    rw [← covariance_self
      (memLp_finsetSum Finset.univ (fun i _ ↦ (hx i).const_mul (a i))).aemeasurable,
      ← covariance_self
        (memLp_finsetSum Finset.univ (fun i _ ↦ (hy i).const_mul (a i))).aemeasurable]
    rw [covariance_fun_sum_fun_sum (fun i ↦ (hx i).const_mul _) (fun i ↦ (hx i).const_mul _),
      covariance_fun_sum_fun_sum (fun i ↦ (hy i).const_mul _) (fun i ↦ (hy i).const_mul _)]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right, hc]
  rw [hmean, hvar]

/-- Full measurable Gaussian paths on different sample spaces have the same uniqueness property. -/
theorem gaussian_cross_space_process_law_eq {Ω Ξ ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ι → Ω → ℝ) (Y : ι → Ξ → ℝ)
    (hX : IsGaussianProcess X μ) (hY : IsGaussianProcess Y ν)
    (hx : Measurable (fun ω i ↦ X i ω)) (hy : Measurable (fun ω i ↦ Y i ω))
    (hm : ∀ i, (∫ ω, X i ω ∂μ) = ∫ ω, Y i ω ∂ν)
    (hc : ∀ i j, cov[X i, X j; μ] = cov[Y i, Y j; ν]) :
    μ.map (fun ω i ↦ X i ω) = ν.map (fun ω i ↦ Y i ω) := by
  classical
  have he (I : Finset ι) : μ.map (fun ω ↦ I.restrict (X · ω)) =
      ν.map (fun ω ↦ I.restrict (Y · ω)) :=
    gaussian_cross_space_finite_law_eq μ ν _ _ (hX.hasGaussianLaw I)
      (hY.hasGaussianLaw I) (fun i ↦ hm i) (fun i j ↦ hc i j)
  have hp := isProjectiveLimit_map (P := μ) hx.aemeasurable
  simp_rw [he] at hp
  exact hp.unique (isProjectiveLimit_map (P := ν) hy.aemeasurable)

end SRWTightness
