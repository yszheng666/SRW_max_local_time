import SRWTightness.ObservationCgfTaylor
import SRWTightness.GreenCovarianceQuadratic

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Every actual finite weighted observation is square integrable. -/
theorem normalizedWeightedSum_memLp_two (D K : Finset Site) (α g u : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (k : ℕ) (w : K → ℝ) :
    MemLp (normalizedWeightedSum K k α g u w) 2 (markProductLaw D K α k) := by
  exact memLp_finsetSum Finset.univ (fun z _ ↦
    (normalizedMarkSum_memLp_two D K α g u hα hcap k z).const_mul (w z))

/-- The directional cgf of the actual observation vector equals half its actual covariance
quadratic form up to the explicit cubic error. -/
theorem observationFamily_cgf_covariance_taylor {ι : Type*} [Fintype ι]
    (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1)
    (w : ι → K → ℝ) (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (b : ι → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ i, |b i|) ≤ (u * Real.sqrt (α * g)) / (8 * L))
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let F := fun i ↦ normalizedWeightedSum K k α g u (w i)
    let μ := markProductLaw D K α k
    |cgf (fun Y ↦ ∑ i, b i * F i Y) μ 1 -
      (∑ i, ∑ j, b i * b j * covariance (F i) (F j) μ) / 2| ≤
        23592976 * L ^ 3 * (∑ i, |b i|) ^ 3 /
          (12 * u * (Real.sqrt (α * g)) ^ 3) := by
  letI := markProductLaw_isProbabilityMeasure D K α hα.le hcap k
  let v := fun z ↦ ∑ i, b i * w i z
  have hf : normalizedWeightedSum K k α g u v =
      (fun Y : MarkSamples K k ↦ ∑ i, b i * normalizedWeightedSum K k α g u (w i) Y) := by
    funext Y
    exact (observation_linear_combination w b (fun z ↦ normalizedMarkSum K k α g u z Y)).symm
  have hq := normalized_green_quadratic_eq_covariance D K hKD α g u hα hg hu hcap v k hk
  dsimp only at hq
  rw [hf, covariance_fun_sum_fun_sum
    (fun i ↦ (normalizedWeightedSum_memLp_two D K α g u hα.le hcap k (w i)).const_mul (b i))
    (fun j ↦ (normalizedWeightedSum_memLp_two D K α g u hα.le hcap k (w j)).const_mul (b j))] at hq
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, ← mul_assoc] at hq
  have ht := observationFamily_cgf_taylor D K hKD α g u hα hg hu hcap w hw hw1 b
    L hL hαL hG hsmall k hk
  dsimp only at ht ⊢
  rw [hq] at ht
  exact ht

end SRWTightness
