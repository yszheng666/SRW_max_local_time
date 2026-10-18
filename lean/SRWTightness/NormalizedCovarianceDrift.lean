import SRWTightness.NormalizedProductCovariance
import SRWTightness.NormalizedMarkTilt
import SRWTightness.ReferenceTiltedWeightedL2
import SRWTightness.ReferenceTiltedCovarianceDrift

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Actual centered normalized observations inherit the one-mark covariance drift. -/
theorem normalizedWeightedSum_covariance_drift (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1)
    (w v : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hv : ∀ z, 0 ≤ v z)
    (hw1 : ∑ z, w z = 1) (hv1 : ∑ z, v z = 1) (b : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hαL : α ≤ L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |b z / (u * Real.sqrt (α * g))|) < 1 / (8 * L)) (k : ℕ) :
    let H := normalizedWeightedSum K k α g u w
    let J := normalizedWeightedSum K k α g u v
    let μ := markProductLaw D K α k
    |covariance H J (μ.tilted (normalizedWeightedSum K k α g u b)) - covariance H J μ| ≤
      k * (35389464 * L ^ 3 * (∑ z, |b z / (u * Real.sqrt (α * g))|)) /
        (u * Real.sqrt (α * g)) / (u * Real.sqrt (α * g)) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα.le hcap
  let μ := referenceMarkLaw D K α
  let β := fun z ↦ b z / (u * Real.sqrt (α * g))
  let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let J := fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)
  have hs : |(1 : ℝ)| * (∑ z, |β z|) < 1 / (8 * L) := by simpa only [abs_one, one_mul] using hsmall
  have hs4 : (∑ z, |β z|) ≤ 1 / (4 * L) :=
    (hsmall.trans (one_div_lt_one_div_of_lt (by positivity) (by linarith))).le
  have hi := (referenceMark_linear_exponential_bound D K hKD α hα.le hcap β L hL hG hs4).1
  letI : IsProbabilityMeasure (μ.tilted X) := isProbabilityMeasure_tilted hi
  have htH : MemLp H 2 (μ.tilted X) := by
    simpa only [one_mul] using
      referenceMark_tilted_weighted_memLp_two D K hKD α hα.le hcap w hw hw1 β L hL hG 1 hs
  have htJ : MemLp J 2 (μ.tilted X) := by
    simpa only [one_mul] using
      referenceMark_tilted_weighted_memLp_two D K hKD α hα.le hcap v hv hv1 β L hL hG 1 hs
  have hH : MemLp H 2 μ := memLp_finsetSum Finset.univ
    (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (w z))
  have hJ : MemLp J 2 μ := memLp_finsetSum Finset.univ
    (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (v z))
  have he := (normalizedWeightedSum_product_tilt D K hKD α g u hα.le hcap b L hL hG hs4 k).2.1
  have hd : 0 < u * Real.sqrt (α * g) := by positivity
  have hb : |covariance H J (μ.tilted X) - covariance H J μ| ≤
      35389464 * L ^ 3 * (∑ z, |β z|) := by
    simpa only [one_mul, abs_one, mul_one] using
      referenceMark_tilted_covariance_drift D K hKD α hα.le hcap w v hw hv hw1 hv1
        β L hL hαL hG 1 hs
  dsimp only
  rw [he]
  change |covariance (normalizedWeightedSum K k α g u w) (normalizedWeightedSum K k α g u v)
      (Measure.pi (fun _ : Fin k ↦ μ.tilted X)) -
    covariance (normalizedWeightedSum K k α g u w) (normalizedWeightedSum K k α g u v)
      (Measure.pi (fun _ : Fin k ↦ μ))| ≤ _
  rw [normalizedWeightedSum_covariance_iid K k α g u _ w v htH htJ,
    normalizedWeightedSum_covariance_iid K k α g u _ w v hH hJ,
    ← sub_div, ← sub_div, ← mul_sub, abs_div, abs_div, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg k), abs_of_pos hd]
  exact div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg k)) hd.le) hd.le

end SRWTightness
