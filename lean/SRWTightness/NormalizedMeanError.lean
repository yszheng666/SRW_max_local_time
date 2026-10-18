import SRWTightness.ReferenceTiltedMeanError
import SRWTightness.NormalizedProductMean
import SRWTightness.NormalizedMarkTilt

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The normalized tilted mean differs from its actual covariance response by a quadratic error. -/
theorem normalizedWeightedSum_mean_error (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hw1 : ∑ z, w z = 1) (b : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hαL : α ≤ L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |b z / (u * Real.sqrt (α * g))|) < 1 / (8 * L)) (k : ℕ) :
    let F := normalizedWeightedSum K k α g u w
    let B := normalizedWeightedSum K k α g u b
    let μ := markProductLaw D K α k
    |(∫ Y, F Y ∂μ.tilted B) - covariance F B μ| ≤
      k * (35389464 * L ^ 3 * (∑ z, |b z / (u * Real.sqrt (α * g))|) ^ 2) /
        (u * Real.sqrt (α * g)) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα.le hcap
  let μ := referenceMarkLaw D K α
  let c := u * Real.sqrt (α * g)
  let β := fun z ↦ b z / c
  let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let J := fun Y : Mark K ↦ ∑ z, b z * (Y z : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hs : |(1 : ℝ)| * (∑ z, |β z|) < 1 / (8 * L) := by simpa using hsmall
  have hs4 : (∑ z, |β z|) ≤ 1 / (4 * L) :=
    (hsmall.trans (one_div_lt_one_div_of_lt (by positivity) (by linarith))).le
  have hi := (referenceMark_linear_exponential_bound D K hKD α hα.le hcap β L hL hG hs4).1
  letI : IsProbabilityMeasure (μ.tilted X) := isProbabilityMeasure_tilted hi
  have htH : MemLp H 2 (μ.tilted X) := by
    simpa only [one_mul] using
      referenceMark_tilted_weighted_memLp_two D K hKD α hα.le hcap w hw hw1 β L hL hG 1 hs
  have hH : MemLp H 2 μ := memLp_finsetSum Finset.univ
    (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (w z))
  have hJ : MemLp J 2 μ := memLp_finsetSum Finset.univ
    (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (b z))
  have he := (normalizedWeightedSum_product_tilt D K hKD α g u hα.le hcap b L hL hG hs4 k).2.1
  have hX : X = (fun Y ↦ J Y / c) := by
    funext Y
    dsimp [X, J, β]
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  have hb : |(∫ Y, H Y ∂μ.tilted X) - α * ∑ z, w z - covariance H J μ / c| ≤
      35389464 * L ^ 3 * (∑ z, |β z|) ^ 2 := by
    have hh := referenceMark_tilted_mean_error D K hKD α hα.le hcap w hw hw1 β
      L hL hαL hG 1 hs
    simp only [one_mul, one_pow, mul_one] at hh
    change |(∫ Y, H Y ∂μ.tilted X) - (∫ Y, H Y ∂μ) - covariance H X μ| ≤ _ at hh
    rw [show (∫ Y, H Y ∂μ) = α * ∑ z, w z from
      referenceMark_linear_mean D K hKD α hα.le hcap w] at hh
    have hcov : covariance H X μ = covariance H J μ / c := by
      rw [hX, covariance_fun_div_right]
    rwa [hcov] at hh
  dsimp only
  rw [he]
  change |(∫ Y, normalizedWeightedSum K k α g u w Y
      ∂Measure.pi (fun _ : Fin k ↦ μ.tilted X)) -
    covariance (normalizedWeightedSum K k α g u w) (normalizedWeightedSum K k α g u b)
      (Measure.pi (fun _ : Fin k ↦ μ))| ≤ _
  rw [normalizedWeightedSum_mean_iid K k α g u _ w htH,
    normalizedWeightedSum_covariance_iid K k α g u _ w b hH hJ]
  have halg (a e q : ℝ) : k * (a - e) / c - k * q / c / c =
      k * (a - e - q / c) / c := by ring
  rw [halg, abs_div, abs_mul, abs_of_pos hc, abs_of_nonneg (Nat.cast_nonneg k)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg k)) hc.le

end SRWTightness
