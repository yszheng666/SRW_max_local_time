import SRWTightness.DyadicLinearGaussian
import SRWTightness.DyadicDistributionLimit

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

theorem gaussianPath_quadratic_limit {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    Tendsto (fun n ↦ ∑ i, ∑ k, a i * a k * min (dyadicTime n (t i)) (dyadicTime n (t k)))
      atTop (nhds (∑ i, ∑ k, a i * a k * min (t i) (t k))) := by
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro k hk
  exact ((dyadicTime_tendsto (t i) (ht i)).min
    (dyadicTime_tendsto (t k) (ht k))).const_mul (a i * a k)

theorem gaussianPath_linear_charFun {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1) (u : ℝ) :
    charFun (gaussianCoefficientLaw.map
      (fun ω ↦ ∑ i, a i * gaussianDyadicPath ω (t i))) u =
      Complex.exp (-((∑ i, ∑ k, a i * a k * min (t i) (t k) : ℝ) : ℂ) *
        (u : ℂ) ^ 2 / 2) := by
  have h1 := gaussianDyadicPath_linear_charFun_limit t a ht u
  have hc : Continuous (fun q : ℝ ↦ Complex.exp (-(q : ℂ) * (u : ℂ) ^ 2 / 2)) := by
    fun_prop
  have h2 := (hc.tendsto _).comp (gaussianPath_quadratic_limit t a ht)
  have he (n : ℕ) : charFun (gaussianCoefficientLaw.map
      (fun ω ↦ ∑ i, a i * gaussianDyadicPath ω (dyadicTime n (t i)))) u =
      Complex.exp (-((∑ i, ∑ k, a i * a k * min (dyadicTime n (t i))
        (dyadicTime n (t k)) : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
    exact dyadicLinear_charFun (fun _ ↦ n) (fun i ↦ dyadicTimeIndex n (t i)) a
      (fun i ↦ dyadicTimeIndex_le n (t i) (ht' i)) u
  simp_rw [he] at h1
  exact tendsto_nhds_unique h1 h2

theorem gaussianPath_quadratic_nonneg {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1) :
    0 ≤ ∑ i, ∑ k, a i * a k * min (t i) (t k) := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (gaussianPath_quadratic_limit t a ht)
  apply Filter.Eventually.of_forall
  intro n
  have h := dyadicLinear_variance (fun _ ↦ n) (fun i ↦ dyadicTimeIndex n (t i)) a
    (fun i ↦ dyadicTimeIndex_le n (t i) (ht' i))
  change 0 ≤ ∑ i, ∑ k, a i * a k *
    min ((dyadicTimeIndex n (t i) : ℝ) / (2 : ℝ) ^ n)
      ((dyadicTimeIndex n (t k) : ℝ) / (2 : ℝ) ^ n)
  rw [← h]
  exact variance_nonneg _ _

theorem gaussianPath_linear_law {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1) :
    gaussianCoefficientLaw.map (fun ω ↦ ∑ i, a i * gaussianDyadicPath ω (t i)) =
      gaussianReal 0 (Real.toNNReal (∑ i, ∑ k, a i * a k * min (t i) (t k))) := by
  apply Measure.ext_of_charFun
  funext u
  rw [gaussianPath_linear_charFun t a ht ht' u, charFun_gaussianReal]
  simp only [Real.coe_toNNReal _ (gaussianPath_quadratic_nonneg t a ht ht'),
    Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  congr 1
  ring

theorem gaussianPath_linear_gaussian {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1) :
    HasGaussianLaw (fun ω ↦ ∑ i, a i * gaussianDyadicPath ω (t i))
      gaussianCoefficientLaw := by
  constructor
  rw [gaussianPath_linear_law t a ht ht']
  infer_instance

end SRWTightness
