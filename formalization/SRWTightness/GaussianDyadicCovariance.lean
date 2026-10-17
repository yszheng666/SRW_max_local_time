import SRWTightness.DyadicCovarianceIdentification

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

theorem gaussianFinitePath_dyadic_stable (m N j : ℕ) (hmN : m ≤ N)
    (ω : GaussianCoefficientSpace) :
    gaussianFinitePath (N, (j : ℝ) / (2 : ℝ) ^ m) ω =
      gaussianDyadicPath ω ((j : ℝ) / (2 : ℝ) ^ m) := by
  unfold gaussianFinitePath gaussianDyadicPath
  congr 1
  symm
  apply tsum_eq_sum
  intro n hn
  exact schauderLevel_dyadic_zero m n j
    (hmN.trans (Nat.le_of_not_gt (by simpa using hn))) _ _

theorem gaussianDyadicPath_dyadic_mean (m j : ℕ) :
    (∫ ω, gaussianDyadicPath ω ((j : ℝ) / (2 : ℝ) ^ m) ∂gaussianCoefficientLaw) = 0 := by
  simp_rw [← gaussianFinitePath_dyadic_stable m m j le_rfl]
  exact gaussianFinitePath_mean m _

theorem gaussianDyadicPath_dyadic_covariance (m l j k : ℕ)
    (hj : j ≤ 2 ^ m) (hk : k ≤ 2 ^ l) :
    cov[fun ω ↦ gaussianDyadicPath ω ((j : ℝ) / (2 : ℝ) ^ m),
      fun ω ↦ gaussianDyadicPath ω ((k : ℝ) / (2 : ℝ) ^ l); gaussianCoefficientLaw] =
      min ((j : ℝ) / (2 : ℝ) ^ m) ((k : ℝ) / (2 : ℝ) ^ l) := by
  let s : ℝ := (j : ℝ) / (2 : ℝ) ^ m
  let t : ℝ := (k : ℝ) / (2 : ℝ) ^ l
  have hs : 0 ≤ s := by positivity
  have ht : 0 ≤ t := by positivity
  have hs' : s ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hj)
  have ht' : t ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hk)
  have hlim : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n / 4) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).div_const 4
  have he : ∀ᶠ n : ℕ in atTop,
      |cov[fun ω ↦ gaussianDyadicPath ω s, fun ω ↦ gaussianDyadicPath ω t;
        gaussianCoefficientLaw] - min s t| ≤ (1 / 2 : ℝ) ^ n / 4 := by
    filter_upwards [eventually_ge_atTop (max m l)] with n hn
    have hm : m ≤ n := (le_max_left _ _).trans hn
    have hl : l ≤ n := (le_max_right _ _).trans hn
    have h := gaussianFinitePath_covariance_error n s t hs hs' ht ht'
    have h1 : gaussianFinitePath (n, s) = fun ω ↦ gaussianDyadicPath ω s :=
      funext (gaussianFinitePath_dyadic_stable m n j hm)
    have h2 : gaussianFinitePath (n, t) = fun ω ↦ gaussianDyadicPath ω t :=
      funext (gaussianFinitePath_dyadic_stable l n k hl)
    rwa [h1, h2] at h
  have hz := le_of_tendsto_of_tendsto tendsto_const_nhds hlim he
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

end SRWTightness
