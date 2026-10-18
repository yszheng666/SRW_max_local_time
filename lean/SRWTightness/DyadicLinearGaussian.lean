import SRWTightness.GaussianDyadicCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem dyadicLinear_gaussian {ι : Type*} [Fintype ι] (m j : ι → ℕ) (a : ι → ℝ) :
    HasGaussianLaw (fun ω ↦ ∑ i, a i *
      gaussianDyadicPath ω ((j i : ℝ) / (2 : ℝ) ^ m i)) gaussianCoefficientLaw := by
  have h := gaussianDyadicPath_dyadic_gaussianProcess.comp_right (fun i ↦ (m i, j i))
  simpa only [smul_eq_mul, Function.comp_def] using
    (h.smul a).hasGaussianLaw_fun_sum (I := Finset.univ)

theorem dyadicLinear_mean {ι : Type*} [Fintype ι] (m j : ι → ℕ) (a : ι → ℝ) :
    (∫ ω, ∑ i, a i * gaussianDyadicPath ω ((j i : ℝ) / (2 : ℝ) ^ m i)
      ∂gaussianCoefficientLaw) = 0 := by
  rw [integral_finsetSum _ (fun i _ ↦
    (gaussianDyadicPath_dyadic_gaussianProcess.hasGaussianLaw_eval (m i, j i)).integrable.const_mul _)]
  simp [integral_const_mul, gaussianDyadicPath_dyadic_mean]

theorem dyadicLinear_variance {ι : Type*} [Fintype ι] (m j : ι → ℕ) (a : ι → ℝ)
    (hj : ∀ i, j i ≤ 2 ^ m i) :
    Var[fun ω ↦ ∑ i, a i * gaussianDyadicPath ω ((j i : ℝ) / (2 : ℝ) ^ m i);
      gaussianCoefficientLaw] =
      ∑ i, ∑ k, a i * a k * min ((j i : ℝ) / (2 : ℝ) ^ m i)
        ((j k : ℝ) / (2 : ℝ) ^ m k) := by
  rw [← covariance_self (dyadicLinear_gaussian m j a).aemeasurable]
  rw [covariance_fun_sum_fun_sum
    (fun i ↦ (gaussianDyadicPath_dyadic_gaussianProcess.hasGaussianLaw_eval
      (m i, j i)).memLp_two.const_mul (a i))
    (fun i ↦ (gaussianDyadicPath_dyadic_gaussianProcess.hasGaussianLaw_eval
      (m i, j i)).memLp_two.const_mul (a i))]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [gaussianDyadicPath_dyadic_covariance _ _ _ _ (hj i) (hj k)]
  ring

theorem dyadicLinear_charFun {ι : Type*} [Fintype ι] (m j : ι → ℕ) (a : ι → ℝ)
    (hj : ∀ i, j i ≤ 2 ^ m i) (u : ℝ) :
    charFun (gaussianCoefficientLaw.map (fun ω ↦ ∑ i, a i *
      gaussianDyadicPath ω ((j i : ℝ) / (2 : ℝ) ^ m i))) u =
      Complex.exp (-((∑ i, ∑ k, a i * a k * min ((j i : ℝ) / (2 : ℝ) ^ m i)
        ((j k : ℝ) / (2 : ℝ) ^ m k) : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
  have hnon : 0 ≤ ∑ i, ∑ k, a i * a k * min ((j i : ℝ) / (2 : ℝ) ^ m i)
      ((j k : ℝ) / (2 : ℝ) ^ m k) := by
    rw [← dyadicLinear_variance m j a hj]
    exact variance_nonneg _ _
  rw [(dyadicLinear_gaussian m j a).map_eq_gaussianReal, dyadicLinear_mean,
    dyadicLinear_variance m j a hj, charFun_gaussianReal]
  simp only [Real.coe_toNNReal _ hnon, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  congr 1
  ring

end SRWTightness
